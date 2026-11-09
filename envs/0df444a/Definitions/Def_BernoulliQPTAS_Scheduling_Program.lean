-- Prove2me | Definitions.Def_BernoulliQPTAS_Scheduling_Program
-- name    : BernoulliQPTAS_Scheduling_Program
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:36.931204+00:00
-- url     : https://prove2.me/theorems/123f6df8-0c0d-4140-a50c-5c3246c42180
-- title:
--   The charged preprocessing programs, the returned table, and table-driven policies
-- statement:
--   This item fixes the computation semantics and writes the algorithms of Theorems 4.6 and 1.1 in it. A computation returns a value and a natural-number charge. Exact rational addition, subtraction, multiplication, division, comparison and ceiling are the only arithmetic, and each is charged the square of the bit lengths of its operands and result, so no unbounded rational operation has unit cost. The input length $L$ is the binary length of $N$, $m$ and the reduced fractions of all $p_j,q_j$. Table access is random access by address, charged the length of the address and of the stored word.
--
--   The program for Theorem 4.6 sorts the jobs into classes by size, probability and label, and runs the memoized recursion of Section 4.3 over every eligible class and both outcomes, storing in each reached state its value, a minimizing job and both successor addresses.
--
--   The program for Theorem 1.1 takes the integer $k=\lceil 1/\eta\rceil$. For $m=1$ it stores the SEPT list. Otherwise it sets $\varepsilon=1/(5k)$,
--
--   $$T=\frac{NP}{\varepsilon},\qquad \sigma=\frac{\varepsilon P}{N^2},\qquad D=\frac{\varepsilon P}{N},$$
--
--   splits the jobs into large, small and medium, rounds each medium size up to the first $\sigma(1+\varepsilon)^e\ge p_j$ by repeated comparison and multiplication, runs the dynamic program with $K=5k$ on the rounded medium jobs, and stores the large-job tests, the fixed list, the small jobs and the wait until $D$.
--
--   The returned policy is defined by a controller: it holds an address and the machine release times, reads one word at that address, starts the named job at the minimum release time on the lowest-labeled machine attaining it, and follows the observed outcome to the next address. A positive job with an actual word releases at its start plus its size; with a reserved word it releases according to the reuse rule on the stored rounded size, shifted by $D$. Completion times remain those of the actual sizes.
-- source:
--   Junho Hwang, STOC 2027 submission #427 (October 2026), Sections 3 and 4.3–4.5, pp.9–14; canonical PDF SHA256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9

import Definitions.Def_BernoulliQPTAS_Scheduling_ReleaseDP

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling

/-! ### The computation semantics, fixed independently of any bound -/

/-- A computed value together with the elementary bit operations charged for it. -/
structure Charged (α : Type) where
  val : α
  cost : ℕ

instance : Monad Charged where
  pure a := ⟨a, 0⟩
  bind x f := ⟨(f x.val).val, x.cost + (f x.val).cost⟩

def tick (c : ℕ) : Charged Unit := ⟨(), c⟩

/-- Binary length of a natural number and of a reduced fraction. -/
def natBits (n : ℕ) : ℕ := Nat.log2 n + 1

def ratBits (q : ℚ) : ℕ := natBits q.num.natAbs + natBits q.den

/-- Exact rational arithmetic: schoolbook multiplication and gcd reduction, so the
    charge is quadratic in the bit lengths of the operands and of the result.
    No rational operation has unit cost. -/
def qOp (f : ℚ → ℚ → ℚ) (a b : ℚ) : Charged ℚ :=
  ⟨f a b, (ratBits a + ratBits b + ratBits (f a b)) ^ 2⟩

def qAdd : ℚ → ℚ → Charged ℚ := qOp (· + ·)
def qSub : ℚ → ℚ → Charged ℚ := qOp (· - ·)
def qMul : ℚ → ℚ → Charged ℚ := qOp (· * ·)
def qDiv : ℚ → ℚ → Charged ℚ := qOp (· / ·)

def qLt (a b : ℚ) : Charged Bool := ⟨decide (a < b), (ratBits a + ratBits b) ^ 2⟩
def qLe (a b : ℚ) : Charged Bool := ⟨decide (a ≤ b), (ratBits a + ratBits b) ^ 2⟩
def qCeil (a : ℚ) : Charged ℤ := ⟨⌈a⌉, ratBits a ^ 2⟩

def readSize {N m : ℕ} (I : Instance N m) (j : Fin N) : Charged ℚ :=
  ⟨I.size j, ratBits (I.size j) + natBits j.val⟩

def readProbability {N m : ℕ} (I : Instance N m) (j : Fin N) : Charged ℚ :=
  ⟨I.probability j, ratBits (I.probability j) + natBits j.val⟩

/-- Binary input length: `N`, `m` and the reduced fractions of all `p_j` and `q_j`. -/
def inputLength {N m : ℕ} (I : Instance N m) : ℕ :=
  natBits N + natBits m + ∑ j, (ratBits (I.size j) + ratBits (I.probability j))

/-- Addresses of the returned table: the three phases of the size reduction, and the
    dynamic-program states `(ℓ, ν)` of Section 4.3. -/
inductive Addr where
  | test (i : ℕ)
  | small (i : ℕ)
  | list (i : ℕ)
  | wait
  | dp (releases : List ℚ) (counts : List ℕ)
  deriving DecidableEq

/-- A stored word: the job to start next (or the waiting time before the shifted
    medium policy), and the addresses to read after a zero and a positive outcome.
    An `actual` job keeps its machine for its size; a `reserved` job keeps its machine
    until the reuse-rule release computed from the stored rounded size. -/
inductive Entry (N : ℕ) where
  | actual (job : Fin N) (size : ℚ) (onZero onPositive : Addr)
  | reserved (job : Fin N) (roundedSize value : ℚ) (onZero onPositive : Addr)
  | idleUntil (time : ℚ) (next : Addr)

def addrBits : Addr → ℕ
  | .test i => natBits i + 1
  | .small i => natBits i + 1
  | .list i => natBits i + 1
  | .wait => 1
  | .dp rs cs => (rs.map ratBits).sum + (cs.map natBits).sum + 1

def entryBits {N : ℕ} : Entry N → ℕ
  | .actual j p z q => natBits j.val + ratBits p + addrBits z + addrBits q
  | .reserved j p v z q => natBits j.val + ratBits p + ratBits v + addrBits z + addrBits q
  | .idleUntil t a => ratBits t + addrBits a

abbrev Table (N : ℕ) := Addr → Option (Entry N)

/-- Programs: charged computation with a random-access table. An access is charged the
    length of its address and of the word transferred. -/
abbrev Prog (N : ℕ) := StateT (Table N) Charged

def run {N : ℕ} {α : Type} (x : Charged α) : Prog N α := fun T => ⟨(x.val, T), x.cost⟩

def memRead {N : ℕ} (a : Addr) : Prog N (Option (Entry N)) := fun T =>
  ⟨(T a, T), addrBits a + (match T a with | some e => entryBits e | none => 0)⟩

def memWrite {N : ℕ} (a : Addr) (e : Entry N) : Prog N Unit := fun T =>
  ⟨((), Function.update T a (some e)), addrBits a + entryBits e⟩

/-! ### The table of the dynamic program, Sections 4.1–4.4 -/

/-- The reuse rule in charged arithmetic; its value is `reuseRat p K s`. -/
def reuseCharged (p : ℚ) (K : ℕ) (s : ℚ) : Charged ℚ := do
  let g ← qDiv p K
  let r ← qDiv s g
  let c ← qCeil r
  let e ← qAdd (c : ℚ) K
  qMul g e

/-- Insert into a sorted vector of release times by charged comparisons. -/
def insertSorted (x : ℚ) : List ℚ → Charged (List ℚ)
  | [] => pure [x]
  | y :: ys => do
      if ← qLe x y then pure (x :: y :: ys)
      else do
        let r ← insertSorted x ys
        pure (y :: r)

/-- One size class: its size and its jobs in the fixed order of Section 2. -/
structure DPClass (N : ℕ) where
  size : ℚ
  jobs : List (Fin N)

structure Candidate (N : ℕ) where
  job : Fin N
  size : ℚ
  value : ℚ
  onZero : Addr
  onPositive : Addr

/-- The minimization of Section 4.3 over all classes with `ν_c > 0`, evaluating both
    outcome successors of every eligible class; ties go to the lowest class number. -/
def bestClass {N m : ℕ} (I : Instance N m) (K : ℕ) (value : List ℚ → List ℕ → Prog N ℚ)
    (rel : List ℚ) (counts : List ℕ) :
    ℕ → List (DPClass N × ℕ) → Option (Candidate N) → Prog N (Option (Candidate N))
  | _, [], best => pure best
  | c, (cl, ν) :: rest, best =>
      match ν, cl.jobs[cl.jobs.length - ν]? with
      | ν' + 1, some j => do
          run (tick (rel.length + counts.length + cl.jobs.length))
          let q ← run (readProbability I j)
          let ℓ₁ := rel.headD 0
          let counts' := counts.set c ν'
          let release ← run (reuseCharged cl.size K ℓ₁)
          let positive ← run (insertSorted release rel.tail)
          let vz ← value rel counts'
          let vp ← value positive counts'
          let own ← run (qMul q cl.size)
          let start ← run (qAdd ℓ₁ own)
          let qz ← run (qSub 1 q)
          let tz ← run (qMul qz vz)
          let tp ← run (qMul q vp)
          let s ← run (qAdd start tz)
          let v ← run (qAdd s tp)
          let cand : Candidate N := ⟨j, cl.size, v, .dp rel counts', .dp positive counts'⟩
          let better ← match best with
            | none => pure true
            | some b => run (qLt v b.value)
          bestClass I K value rel counts (c + 1) rest (if better then some cand else best)
      | _, _ => bestClass I K value rel counts (c + 1) rest best

/-- The memoized Bellman recursion: every reachable state is expanded once, and its
    value, minimizing job and both successor addresses are stored. -/
def solve {N m : ℕ} (I : Instance N m) (K : ℕ) (classes : List (DPClass N)) :
    ℕ → List ℚ → List ℕ → Prog N ℚ
  | 0, _, _ => pure 0
  | fuel + 1, rel, counts => do
      run (tick (counts.length + 1))
      if counts.all (· == 0) then pure 0
      else do
        match ← memRead (.dp rel counts) with
        | some (.reserved _ _ v _ _) => pure v
        | _ => do
            match ← bestClass I K (solve I K classes fuel) rel counts 0
                (classes.zip counts) none with
            | none => pure 0
            | some c => do
                memWrite (.dp rel counts) (.reserved c.job c.size c.value c.onZero c.onPositive)
                pure c.value

/-- Size, then probability, then job label. -/
def classLe {N : ℕ} (a b : ℚ × ℚ × Fin N) : Charged Bool :=
  ⟨decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 ≤ b.2.2)))),
    (ratBits a.1 + ratBits a.2.1 + natBits a.2.2.val +
      ratBits b.1 + ratBits b.2.1 + natBits b.2.2.val) ^ 2⟩

def insertBy {α : Type} (le : α → α → Charged Bool) (x : α) : List α → Charged (List α)
  | [] => pure [x]
  | y :: ys => do
      if ← le x y then pure (x :: y :: ys)
      else do
        let r ← insertBy le x ys
        pure (y :: r)

/-- Insertion sort by charged comparisons. -/
def sortBy {α : Type} (le : α → α → Charged Bool) : List α → Charged (List α)
  | [] => pure []
  | x :: xs => do
      let r ← sortBy le xs
      insertBy le x r

/-- Split a list sorted by `classLe` into its size classes. -/
def groupClasses {N : ℕ} : List (ℚ × ℚ × Fin N) → List (DPClass N)
  | [] => []
  | x :: xs =>
      match groupClasses xs with
      | c :: cs => if c.size = x.1 then ⟨c.size, x.2.2 :: c.jobs⟩ :: cs
          else ⟨x.1, [x.2.2]⟩ :: c :: cs
      | [] => [⟨x.1, [x.2.2]⟩]

/-- Build the table of the dynamic program for the given job sizes, with all machines
    released at time 0, and return the address of its root state. -/
def buildDP {N m : ℕ} (I : Instance N m) (K : ℕ) (sized : List (ℚ × Fin N)) : Prog N Addr := do
  let triples ← run (sized.mapM fun x => do
    let q ← readProbability I x.2
    pure (x.1, q, x.2))
  let sorted ← run (sortBy classLe triples)
  run (tick ((sorted.map fun x => ratBits x.1 + natBits x.2.2.val).sum))
  let classes := groupClasses sorted
  let counts := classes.map fun c => c.jobs.length
  let releases := List.replicate m (0 : ℚ)
  run (tick (m + classes.length))
  let _ ← solve I K classes sized.length releases counts
  pure (.dp releases counts)

/-- What a preprocessing run returns: the table, the address of the first decision, and
    the grid parameter and time shift that the controller uses to maintain releases. -/
structure Compiled (N : ℕ) where
  table : Table N
  root : Addr
  gridK : ℕ
  offset : ℚ

def emptyTable (N : ℕ) : Table N := fun _ => none

/-- The program of Theorem 4.6: read the instance and build the table. -/
def computeRoundedPolicy {N m : ℕ} (I : Instance N m) (K : ℕ) : Charged (Compiled N) := do
  let sized ← (List.finRange N).mapM fun j => do
    let p ← readSize I j
    pure (p, j)
  let r ← (buildDP I K sized).run (emptyTable N)
  pure ⟨r.2, r.1, K, 0⟩

/-! ### The preprocessing of Sections 3 and 4.5 -/

/-- The expected total processing time, in charged arithmetic. -/
def meanCharged {N m : ℕ} (I : Instance N m) : Charged ℚ :=
  (List.finRange N).foldlM (fun acc j => do
    let p ← readSize I j
    let q ← readProbability I j
    let μ ← qMul q p
    qAdd acc μ) 0

/-- Multiply by `base` until `p` is reached: the smallest `σ * base ^ e ≥ p`, computed by
    rational comparisons and products, with no logarithm oracle. -/
def roundUp (base p : ℚ) : ℕ → ℚ → Charged ℚ
  | 0, x => pure x
  | fuel + 1, x => do
      if ← qLt x p then
        let y ← qMul x base
        roundUp base p fuel y
      else pure x

/-- Store a run of list-scheduling decisions at consecutive addresses. -/
def writeRun {N m : ℕ} (I : Instance N m) (addr : ℕ → Addr) (after : Addr) :
    ℕ → List (Fin N) → Prog N Unit
  | _, [] => pure ()
  | i, j :: rest => do
      let p ← run (readSize I j)
      let next := if rest.isEmpty then after else addr (i + 1)
      memWrite (addr i) (.actual j p next next)
      writeRun I addr after (i + 1) rest

/-- Store the large-job tests: a positive outcome of the `i`-th large job continues with
    the fixed list at position `i + 1`, a zero outcome with the next test. -/
def writeTests {N m : ℕ} (I : Instance N m) (after : Addr) :
    ℕ → List (Fin N) → Prog N Unit
  | _, [] => pure ()
  | i, j :: rest => do
      let p ← run (readSize I j)
      memWrite (.test i) (.actual j p (if rest.isEmpty then after else .test (i + 1)) (.list (i + 1)))
      writeTests I after (i + 1) rest

/-- Split jobs by a charged test, keeping their order. -/
def partitionCharged {α : Type} (test : α → Charged Bool) :
    List α → Charged (List α × List α)
  | [] => pure ([], [])
  | x :: xs => do
      let r ← partitionCharged test xs
      if ← test x then pure (x :: r.1, r.2) else pure (r.1, x :: r.2)

/-- `m = 1`, p.9: SEPT, the fixed order of nondecreasing `q_j p_j`. -/
def septProgram {N m : ℕ} (I : Instance N m) : Prog N Addr := do
  let keyed ← run ((List.finRange N).mapM fun j => do
    let p ← readSize I j
    let q ← readProbability I j
    let μ ← qMul q p
    pure (μ, (0 : ℚ), j))
  let sorted ← run (sortBy classLe keyed)
  writeRun I Addr.list (.list N) 0 (sorted.map fun x => x.2.2)
  pure (.list 0)

/-- `2 ≤ m < N`, Sections 3 and 4.5: thresholds for `ε = 1/(5k)`, the large tests, the
    fixed list, the small jobs, the wait until `D`, and the dynamic program with
    `K = 5k` on the medium jobs with sizes rounded up to `σ (1+ε)^e`. -/
def reductionProgram {N m : ℕ} (I : Instance N m) (k : ℕ) : Prog N (Addr × ℚ) := do
  let P ← run (meanCharged I)
  let ε : ℚ := 1 / (5 * k : ℕ)
  run (tick (natBits N + natBits k))
  let NP ← run (qMul N P)
  let T ← run (qDiv NP ε)
  let εP ← run (qMul ε P)
  let N2 ← run (qMul N N)
  let σ ← run (qDiv εP N2)
  let D ← run (qDiv εP N)
  let base ← run (qAdd 1 ε)
  let splitLarge ← run (partitionCharged (fun j => do qLe T (← readSize I j)) (List.finRange N))
  let large := splitLarge.1
  let splitSmall ← run (partitionCharged (fun j => do qLt (← readSize I j) σ) splitLarge.2)
  let small := splitSmall.1
  let medium := splitSmall.2
  let fuel := N ^ 3 * (5 * k) ^ 3 + 1
  run (tick (natBits fuel + N))
  let rounded ← run (medium.mapM fun j => do
    let p ← readSize I j
    let p' ← roundUp base p fuel σ
    pure (p', j))
  let dpRoot ← buildDP I (5 * k) rounded
  memWrite .wait (.idleUntil D dpRoot)
  let afterLarge : Addr := if small.isEmpty then .wait else .small 0
  writeRun I Addr.small .wait 0 small
  writeRun I Addr.list (.list N) 0 (large ++ small ++ medium)
  writeTests I afterLarge 0 large
  pure (if large.isEmpty then afterLarge else .test 0, D)

/-- The program of Theorem 1.1. The accuracy is supplied as the integer `k = ⌈1/η⌉`. -/
def qptasProgram {N m : ℕ} (I : Instance N m) (k : ℕ) : Charged (Compiled N) :=
  if m = 1 then do
    let r ← (septProgram I).run (emptyTable N)
    pure ⟨r.2, r.1, 1, 0⟩
  else do
    let r ← (reductionProgram I k).run (emptyTable N)
    pure ⟨r.2, r.1.1, 5 * k, r.1.2⟩

/-! ### The returned policy -/

/-- `t` is the policy whose every decision is one read of the returned table.
    The controller maintains only the current address and the machine release times:
    it reads the word at the address; the word names the job; the job starts on the
    machine of minimum release (lowest label on ties) at that release time; the next
    address and the machine's new release follow the observed outcome. Reading an
    `idleUntil` word waits and starts no job. An unwritten address ends the policy. -/
def LookupPolicy {N m : ℕ} (out : Compiled N) :
    ℕ → Addr → (Fin m → ℚ) → PolicyTree N m → Prop
  | 0, _, _, t => t = .done
  | fuel + 1, addr, free, t =>
      match out.table addr with
      | none => t = .done
      | some (.idleUntil u next) => LookupPolicy out fuel next (fun i => max (free i) u) t
      | some (.actual j p z q) =>
          ∃ i tz tp, firstMachine (⟨free, ∅⟩ : PhysicalDPState N m) = some i ∧
            t = .start ⟨j, i, Real.toNNReal (free i : ℝ)⟩ tz tp ∧
            LookupPolicy out fuel z free tz ∧
            LookupPolicy out fuel q (Function.update free i (free i + p)) tp
      | some (.reserved j p _ z q) =>
          ∃ i tz tp, firstMachine (⟨free, ∅⟩ : PhysicalDPState N m) = some i ∧
            t = .start ⟨j, i, Real.toNNReal (free i : ℝ)⟩ tz tp ∧
            LookupPolicy out fuel z free tz ∧
            LookupPolicy out fuel q (Function.update free i
              (out.offset + reuseRat p out.gridK (free i - out.offset))) tp

end BernoulliQPTAS.Scheduling


