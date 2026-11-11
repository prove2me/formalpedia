-- Prove2me | Definitions.Def_SparseLowFactors_BoundedDeg_Machine
-- name    : SparseLowFactors_BoundedDeg_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:23:45.485688+00:00
-- url     : https://prove2.me/theorems/7678e9c6-ad79-4062-9f17-3e97f0d19f7b
-- title:
--   Deterministic algebraic RAM with univariate factorization; input and output layouts
-- statement:
--   The paper's algorithms are deterministic, count field operations at unit cost (p. 15), and use univariate factorization as a black box of cost $T(F,d)$ (Definition 2.11, Remarks 1.2 and 4.2). They are formalized as programs for the following machine over a field $K$.
--
--   1. **Memory.** Word cells $W[i]$ holding $w$-bit words and field cells $F[i]$ holding elements of $K$, both indexed by $\mathbb Z$.
--   2. **Instructions.** Those of the published algebraic RAM `MatroidSensOracle_AlgRAM` without its coin: word constants and $+,-,\times$, unsigned division and remainder, indirect load and store, the branch "if $W[i]<0$"; field constants $0,1$, $+,-,\times$, inversion ($0^{-1}=0$), indirect load and store with addresses in word cells, the branch "if $F[i]=0$"; and `halt`. Two instructions are added:
--      - `factor`: the polynomial $q=\sum_{t<\ell}F[a+t]Y^t$ is handed to a **factorization oracle**, which returns $c$ and pairs $(p_k,m_k)$; the machine writes $r,\deg p_1,m_1,\dots,\deg p_r,m_r$ to word cells and $c$ and the coefficients of the $p_k$ to field cells. A valid oracle answers every $q\neq0$ with its irreducible factorization: distinct monic irreducible $p_k$, $m_k\ge1$, $c\prod_kp_k^{m_k}=q$, in any order.
--      - `elem`: $F[i]:=e(W[j])$ for an enumeration $e:\mathbb N\to K$ injective on $\{0,\dots,|K|-1\}$ (on $\mathbb N$ if $K$ is infinite), the "fixed standard enumeration" of footnote 7, p. 25.
--   3. **Cost.** Every executed instruction, including `halt`, is one step. A run also reports the number of `factor` calls and the largest degree of a polynomial passed to `factor`.
--   4. **Input.** A sparse polynomial $f=\sum_{j=1}^{s'}c_jX^{\alpha_j}$ (distinct $\alpha_j$, $c_j\neq0$, any order) is given by the words $(\text{header}, s', \alpha_{1,1},\dots,\alpha_{1,n},\alpha_{2,1},\dots)$ from cell $0$ and the coefficients $c_1,\dots,c_{s'}$ from field cell $0$. A circuit given as input is the words $N$, root, then for each node its kind ($0$ variable, $1$ constant, $2$ addition, $3$ multiplication, $4$ division), its argument and its children, and one field cell per node holding its constant.
--   5. **Output.** At halting, $W[0]$ points to the output. A circuit in memory has a descriptor (number of nodes, root, then one record address per node; a record holds kind, argument and children); a list is its length followed by descriptor addresses. Decoding fails unless every record is well formed and every child of a node precedes it.
--
--   **Formalization Note** Statements quantify over every valid oracle and every admissible enumeration, so neither can carry information about the instance; the program is fixed before the field and the instance. $T(F,d)$ is accounted for by counting each `factor` call as one step and requiring every call to be on a polynomial of degree at most $d$. Word length is a parameter $w$; statements require $w\ge C\log_2(\cdots)$, enough for indices and counters but not for encoding field data in words.
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 15 (conventions), p. 19 (Definition 2.11), p. 5 (Remark 1.2), p. 33 (Remark 4.2), p. 25 (footnote 7)

import Mathlib
import Definitions.Def_SetMultCost_Circuit
import Definitions.Def_SparseLowFactors_BoundedDeg_Circuits

set_option autoImplicit false

/-!
# The deterministic algebraic RAM with univariate factorization, and its input/output layouts

Bhattacharjee, Kothary, Rai, Saraf, arXiv:2606.27293 (held version, sha256 9837a932…). The paper
names no machine model; its conventions are: unit-cost field operations (bit-complexity convention,
p. 15), univariate factorization as a black box of cost `T(F, d)` (Definition 2.11 p. 19, Remarks 1.2
p. 5 and 4.2 p. 33), and "the first `m` elements in the field, according to some fixed standard
enumeration" (footnote 7, p. 25).

**Formalization Note.**
* **Machine.** The instruction pattern of the published algebraic RAM `MatroidSensOracle_AlgRAM`
  (word cells `ℤ → BitVec w`, field cells `ℤ → K`; word instructions `one add sub mul udiv umod load
  store bltz`; field instructions `fzero fone fadd fsub fmul finv` (`0⁻¹ = 0`), `fload fstore`
  (addresses from word cells, read signed), the zero test `fbz`; `halt`; fetching past the end
  halts), **without** its coin, plus two unit-cost instructions:
  - `factor a l wo fo`: the polynomial `q = Σ_{t < W[l]} F[W[a] + t] Y^t` is factored by the oracle
    `fac`, answering `(c, [(p_1, m_1), …, (p_r, m_r)])`; the machine writes `r, deg p_1, m_1, …,
    deg p_r, m_r` to the word cells from `W[wo]` on and `c` followed by the coefficients
    `0, …, deg p_k` of each `p_k` to the field cells from `W[fo]` on.
  - `elem i j`: `F[i] := e(W[j])` for the enumeration `e : ℕ → K`.
* **Oracles are adversarial.** Statements quantify over every `fac` satisfying `FactorOracle.Valid`
  (for `q ≠ 0`: distinct monic irreducible `p_k`, multiplicities `≥ 1`, `c ∏ p_k^{m_k} = q`, any
  order) and every `e` satisfying `EnumOK` (injective on `{0, …, |K| − 1}`, on `ℕ` if `K` is infinite).
* **Cost.** Every executed instruction, `halt` included, is one step. `exec` also returns the number
  of `factor` calls and the largest degree of a polynomial passed to `factor`: `T(F, d)` is accounted
  for by counting a call as one step and requiring every call to have degree at most `d`.
-/

namespace SparseLowFactors.BoundedDeg

open SetMultCost

/-- Instructions; `i j k a l wo fo` name cells, `l` in `bltz`/`fbz` a program position. -/
inductive Instr where
  | one (i : ℤ)
  | add (i j k : ℤ)
  | sub (i j k : ℤ)
  | mul (i j k : ℤ)
  | udiv (i j k : ℤ)
  | umod (i j k : ℤ)
  | load (i j : ℤ)
  | store (i j : ℤ)
  | bltz (i : ℤ) (l : ℕ)
  | fzero (i : ℤ)
  | fone (i : ℤ)
  | fadd (i j k : ℤ)
  | fsub (i j k : ℤ)
  | fmul (i j k : ℤ)
  | finv (i j : ℤ)
  | fload (i j : ℤ)
  | fstore (i j : ℤ)
  | fbz (i : ℤ) (l : ℕ)
  | elem (i j : ℤ)
  | factor (a l wo fo : ℤ)
  | halt

/-- A univariate factorization oracle over `K`: `q ↦ (c, [(p_k, m_k)])`. -/
abbrev FactorOracle (K : Type) [Field K] := Polynomial K → K × List (Polynomial K × ℕ)

/-- The oracle answers every non-zero `q` with its irreducible factorization: distinct monic
irreducible factors with multiplicities at least `1` and `c ∏ p_k^{m_k} = q` (any order). -/
def FactorOracle.Valid {K : Type} [Field K] (fac : FactorOracle K) : Prop :=
  ∀ q : Polynomial K, q ≠ 0 →
    Polynomial.C (fac q).1 * ((fac q).2.map fun pm => pm.1 ^ pm.2).prod = q ∧
    (∀ pm ∈ (fac q).2, pm.1.Monic ∧ Irreducible pm.1 ∧ 1 ≤ pm.2) ∧
    ((fac q).2.map Prod.fst).Nodup

/-- The fixed enumeration of field elements (footnote 7, p. 25) is injective on
`{0, …, |K| − 1}` (on all of `ℕ` when `K` is infinite, where `Nat.card K = 0`). -/
def EnumOK {K : Type} (e : ℕ → K) : Prop :=
  ∀ a b : ℕ, (Nat.card K = 0 ∨ (a < Nat.card K ∧ b < Nat.card K)) → e a = e b → a = b

/-- Write the list `vs` into the cells `base, base + 1, …` of a memory. -/
def writeList {V : Type} (m : ℤ → V) (base : ℤ) (vs : List V) : ℤ → V :=
  fun x => if base ≤ x ∧ x < base + vs.length then vs.getD (x - base).toNat (m x) else m x

/-- The words the `factor` instruction writes: `r, deg p_1, m_1, …, deg p_r, m_r`. -/
noncomputable def factorWords {K : Type} [Field K] (w : ℕ) (ans : K × List (Polynomial K × ℕ)) :
    List (BitVec w) :=
  BitVec.ofNat w ans.2.length ::
    ans.2.flatMap fun pm => [BitVec.ofNat w pm.1.natDegree, BitVec.ofNat w pm.2]

/-- The field elements the `factor` instruction writes: `c`, then the coefficients `0, …, deg p_k`
of each factor in turn. -/
noncomputable def factorFields {K : Type} [Field K] (ans : K × List (Polynomial K × ℕ)) : List K :=
  ans.1 :: ans.2.flatMap fun pm => (List.range (pm.1.natDegree + 1)).map fun t => pm.1.coeff t

/-- The state at halting: word memory, field memory, number of `factor` calls, and the largest
degree of a polynomial passed to `factor`. -/
structure Result (K : Type) (w : ℕ) where
  wm : ℤ → BitVec w
  fm : ℤ → K
  facCalls : ℕ
  facMaxDeg : ℕ

open Classical in
/-- Run `P` from position `pc` for at most `t` steps; `some` the halting state if it halts within
`t` steps (each executed instruction, `halt` included, costs one step), `none` otherwise. -/
noncomputable def exec {K : Type} [Field K] {w : ℕ} (P : List Instr) (fac : FactorOracle K)
    (e : ℕ → K) : (t pc calls md : ℕ) → (wm : ℤ → BitVec w) → (fm : ℤ → K) → Option (Result K w)
  | 0, _, _, _, _, _ => none
  | t + 1, pc, calls, md, wm, fm =>
    let wwrite (i : ℤ) (v : BitVec w) :=
      exec P fac e t (pc + 1) calls md (fun x => if x = i then v else wm x) fm
    let fwrite (i : ℤ) (v : K) :=
      exec P fac e t (pc + 1) calls md wm (fun x => if x = i then v else fm x)
    match P.getD pc .halt with
    | .one i => wwrite i 1
    | .add i j k => wwrite i (wm j + wm k)
    | .sub i j k => wwrite i (wm j - wm k)
    | .mul i j k => wwrite i (wm j * wm k)
    | .udiv i j k => wwrite i (wm j / wm k)
    | .umod i j k => wwrite i (wm j % wm k)
    | .load i j => wwrite i (wm (wm j).toInt)
    | .store i j => wwrite (wm i).toInt (wm j)
    | .bltz i l => exec P fac e t (if (wm i).toInt < 0 then l else pc + 1) calls md wm fm
    | .fzero i => fwrite i 0
    | .fone i => fwrite i 1
    | .fadd i j k => fwrite i (fm j + fm k)
    | .fsub i j k => fwrite i (fm j - fm k)
    | .fmul i j k => fwrite i (fm j * fm k)
    | .finv i j => fwrite i (fm j)⁻¹
    | .fload i j => fwrite i (fm (wm j).toInt)
    | .fstore i j => fwrite (wm i).toInt (fm j)
    | .fbz i l => exec P fac e t (if fm i = 0 then l else pc + 1) calls md wm fm
    | .elem i j => fwrite i (e (wm j).toNat)
    | .factor a l wo fo =>
      let q : Polynomial K := ∑ t ∈ Finset.range (wm l).toNat,
        Polynomial.monomial t (fm ((wm a).toInt + t))
      let ans := fac q
      exec P fac e t (pc + 1) (calls + 1) (max md q.natDegree)
        (writeList wm (wm wo).toInt (factorWords w ans))
        (writeList fm (wm fo).toInt (factorFields ans))
    | .halt => some ⟨wm, fm, calls, md⟩

/-- Run `P` on the initial memories for at most `t` steps. -/
noncomputable def run {K : Type} [Field K] {w : ℕ} (P : List Instr) (fac : FactorOracle K)
    (e : ℕ → K) (t : ℕ) (wm : ℤ → BitVec w) (fm : ℤ → K) : Option (Result K w) :=
  exec P fac e t 0 0 0 wm fm

/-- The word memory at the start: the integers `ws` in cells `0, 1, …`, `0` elsewhere. -/
def loadWords (w : ℕ) (ws : List ℤ) : ℤ → BitVec w :=
  fun a => if a < 0 then 0 else BitVec.ofInt w (ws.getD a.toNat 0)

/-- The field memory at the start: the elements `xs` in cells `0, 1, …`, `0` elsewhere. -/
def loadFields {K : Type} [Field K] (xs : List K) : ℤ → K :=
  fun a => if a < 0 then 0 else xs.getD a.toNat 0

/-! ## Input: sparse representations and circuits -/

/-- `terms = [(c_1, α_1), …, (c_{s'}, α_{s'})]` is a sparse representation of `f`: distinct exponent
vectors, non-zero coefficients, and `f = Σ_j c_j X^{α_j}` (any order of the terms). -/
def IsSparseRep {n : ℕ} {F : Type} [Field F] (f : MvPolynomial (Fin n) F)
    (terms : List (F × (Fin n → ℕ))) : Prop :=
  (terms.map Prod.snd).Nodup ∧ (∀ t ∈ terms, t.1 ≠ 0) ∧
    f = (terms.map fun t => MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm t.2) t.1).sum

/-- Input words of a sparse polynomial: the header (e.g. `[n, s, d]`), then the number of terms,
then the exponent vectors `α_{1,1}, …, α_{1,n}, α_{2,1}, …` in the order of `terms`. -/
def sparseWords {n : ℕ} {F : Type} (header : List ℤ) (terms : List (F × (Fin n → ℕ))) : List ℤ :=
  header ++ [(terms.length : ℤ)] ++ terms.flatMap fun t => (List.finRange n).map fun i => (t.2 i : ℤ)

/-- Input field cells of a sparse polynomial over `F`, run over `K ⊇ F`: the coefficients
`c_1, …, c_{s'}` mapped into `K`, in the order of `terms`. -/
def sparseFields {n : ℕ} {F K : Type} [Field F] [Field K] [Algebra F K]
    (terms : List (F × (Fin n → ℕ))) : List K :=
  terms.map fun t => algebraMap F K t.1

/-- The words of a division-free circuit given as input: `numNodes, root`, then for every node in
order its kind (`0` variable, `1` constant, `2` addition, `3` multiplication) and argument (the
variable index; `0` for a constant; the number of children for a gate) followed by its children.
The constant of node `v` (or `0` for a non-constant node) is field cell `v` of `circuitFields`. -/
def circuitWords {σ K : Type} (idx : σ → ℕ) (Φ : Circuit σ K) : List ℤ :=
  [(Φ.numNodes : ℤ), (Φ.root : ℤ)] ++ (List.finRange Φ.numNodes).flatMap fun v =>
    match Φ.gate v with
    | .var x => [0, (idx x : ℤ)]
    | .const _ => [1, 0]
    | .add cs => [2, (cs.length : ℤ)] ++ cs.map fun c => (c : ℤ)
    | .mul cs => [3, (cs.length : ℤ)] ++ cs.map fun c => (c : ℤ)

/-- The field cells of a division-free circuit given as input (see `circuitWords`). -/
def circuitFields {σ K : Type} [Field K] (Φ : Circuit σ K) : List K :=
  (List.finRange Φ.numNodes).map fun v =>
    match Φ.gate v with
    | .const a => a
    | _ => 0

/-- The words of a circuit with division gates given as input: as `circuitWords`, with kind `4`
for a division gate followed by `2, num, den`. -/
def divCircuitWords {σ K : Type} (idx : σ → ℕ) (Φ : DivCircuit σ K) : List ℤ :=
  [(Φ.numNodes : ℤ), (Φ.root : ℤ)] ++ (List.finRange Φ.numNodes).flatMap fun v =>
    match Φ.gate v with
    | .var x => [0, (idx x : ℤ)]
    | .const _ => [1, 0]
    | .add cs => [2, (cs.length : ℤ)] ++ cs.map fun c => (c : ℤ)
    | .mul cs => [3, (cs.length : ℤ)] ++ cs.map fun c => (c : ℤ)
    | .div a b => [4, 2, (a : ℤ), (b : ℤ)]

/-- The field cells of a circuit with division gates given as input. -/
def divCircuitFields {σ K : Type} [Field K] (Φ : DivCircuit σ K) : List K :=
  (List.finRange Φ.numNodes).map fun v =>
    match Φ.gate v with
    | .const a => a
    | _ => 0

/-! ## Output: circuits written in memory

A circuit in memory has a descriptor at word address `c`: `W[c]` = number of nodes `N`,
`W[c+1]` = root, and `W[c+2+v]` = the address `p_v` of node `v`'s record. The record is
`W[p_v]` = kind (`0` variable, `1` constant, `2` addition, `3` multiplication, `4` division),
`W[p_v+1]` = argument (variable index; field address of the constant; number of children), and
`W[p_v+2+t]` = child `t`. Decoding fails (`none`) unless the root is a node, every variable index
is `< n`, every child of a node `v` is `< v`, and a division gate has exactly two children. -/

/-- The children of a record, keeping those `< v` (all of them when decoding succeeds). -/
def keepBelow {N : ℕ} (v : Fin N) (cs : List ℕ) : List (Fin N) :=
  cs.filterMap fun c => if h : c < v.val then some ⟨c, h.trans v.isLt⟩ else none

theorem mem_keepBelow {N : ℕ} {v : Fin N} {cs : List ℕ} {c : Fin N} (h : c ∈ keepBelow v cs) :
    c < v := by
  unfold keepBelow at h
  rw [List.mem_filterMap] at h
  obtain ⟨a, _, ha⟩ := h
  split at ha
  · cases ha; assumption
  · cases ha

/-- The address of node `v`'s record, its kind, argument and children. -/
def recAddr {w : ℕ} (wm : ℤ → BitVec w) (c : ℤ) (v : ℕ) : ℤ := (wm (c + 2 + v)).toInt
def recKind {w : ℕ} (wm : ℤ → BitVec w) (c : ℤ) (v : ℕ) : ℕ := (wm (recAddr wm c v)).toNat
def recArg {w : ℕ} (wm : ℤ → BitVec w) (c : ℤ) (v : ℕ) : ℕ := (wm (recAddr wm c v + 1)).toNat
def recKids {w : ℕ} (wm : ℤ → BitVec w) (c : ℤ) (v : ℕ) : List ℕ :=
  (List.range (recArg wm c v)).map fun t => (wm (recAddr wm c v + 2 + t)).toNat

/-- The gate of node `v` of a division-free circuit record. -/
def mkGate {K : Type} {w : ℕ} (n : ℕ) (wm : ℤ → BitVec w) (fm : ℤ → K) (c : ℤ) {N : ℕ}
    (v : Fin N) : Gate (Fin n) K (Fin N) :=
  match recKind wm c v with
  | 0 => if h : recArg wm c v < n then .var ⟨recArg wm c v, h⟩ else .const (fm 0)
  | 1 => .const (fm (wm (recAddr wm c v + 1)).toInt)
  | 2 => .add (keepBelow v (recKids wm c v))
  | _ => .mul (keepBelow v (recKids wm c v))

theorem mkGate_acyclic {K : Type} {w : ℕ} (n : ℕ) (wm : ℤ → BitVec w) (fm : ℤ → K) (c : ℤ)
    {N : ℕ} (v : Fin N) : ∀ x ∈ (mkGate n wm fm c v).children, x < v := by
  intro x hx
  unfold mkGate at hx
  split at hx
  · split at hx <;> simp [Gate.children] at hx
  · simp [Gate.children] at hx
  · exact mem_keepBelow hx
  · exact mem_keepBelow hx

open Classical in
/-- Decode the division-free circuit with descriptor at word address `c`, variables `X_0 … X_{n-1}`. -/
noncomputable def decodeCircuit {K : Type} {w : ℕ} (n : ℕ) (wm : ℤ → BitVec w) (fm : ℤ → K)
    (c : ℤ) : Option (Circuit (Fin n) K) :=
  let N := (wm c).toNat
  let root := (wm (c + 1)).toNat
  if h : root < N ∧ ∀ v < N, recKind wm c v ≤ 3 ∧ (recKind wm c v = 0 → recArg wm c v < n) ∧
      (2 ≤ recKind wm c v → ∀ x ∈ recKids wm c v, x < v) then
    some { numNodes := N, gate := fun v => mkGate n wm fm c v,
           acyclic := fun v => mkGate_acyclic n wm fm c v, root := ⟨root, h.1⟩ }
  else none

/-- The gate of node `v` of a record of a circuit with division gates. -/
def mkDGate {K : Type} {w : ℕ} (n : ℕ) (wm : ℤ → BitVec w) (fm : ℤ → K) (c : ℤ) {N : ℕ}
    (v : Fin N) : DGate (Fin n) K (Fin N) :=
  match recKind wm c v with
  | 0 => if h : recArg wm c v < n then .var ⟨recArg wm c v, h⟩ else .const (fm 0)
  | 1 => .const (fm (wm (recAddr wm c v + 1)).toInt)
  | 2 => .add (keepBelow v (recKids wm c v))
  | 3 => .mul (keepBelow v (recKids wm c v))
  | _ =>
    match keepBelow v (recKids wm c v) with
    | [a, b] => .div a b
    | _ => .const (fm 0)

theorem mkDGate_acyclic {K : Type} {w : ℕ} (n : ℕ) (wm : ℤ → BitVec w) (fm : ℤ → K) (c : ℤ)
    {N : ℕ} (v : Fin N) : ∀ x ∈ (mkDGate n wm fm c v).children, x < v := by
  intro x hx
  unfold mkDGate at hx
  split at hx
  · split at hx <;> simp [DGate.children] at hx
  · simp [DGate.children] at hx
  · exact mem_keepBelow hx
  · exact mem_keepBelow hx
  · split at hx
    · rename_i a b hab
      have hx' : x ∈ keepBelow v (recKids wm c v) := by
        rw [hab]; simpa [DGate.children] using hx
      exact mem_keepBelow hx'
    · simp [DGate.children] at hx

open Classical in
/-- Decode the circuit with division gates with descriptor at word address `c`. -/
noncomputable def decodeDivCircuit {K : Type} {w : ℕ} (n : ℕ) (wm : ℤ → BitVec w) (fm : ℤ → K)
    (c : ℤ) : Option (DivCircuit (Fin n) K) :=
  let N := (wm c).toNat
  let root := (wm (c + 1)).toNat
  if h : root < N ∧ ∀ v < N, recKind wm c v ≤ 4 ∧ (recKind wm c v = 0 → recArg wm c v < n) ∧
      (2 ≤ recKind wm c v → ∀ x ∈ recKids wm c v, x < v) ∧
      (recKind wm c v = 4 → recArg wm c v = 2) then
    some { numNodes := N, gate := fun v => mkDGate n wm fm c v,
           acyclic := fun v => mkDGate_acyclic n wm fm c v, root := ⟨root, h.1⟩ }
  else none

/-- A list in memory at word address `a`: `W[a]` = its length `m`, and `W[a+1+k]` the descriptor
address of entry `k`, decoded by `dec`. -/
def decodeList {α : Type} {w : ℕ} (wm : ℤ → BitVec w) (a : ℤ) (dec : ℤ → Option α) :
    Option (List α) :=
  (List.range (wm a).toNat).mapM fun k => dec (wm (a + 1 + k)).toInt

/-- The output pointer: word cell `0` at halting holds the address of the output. -/
def outPtr {w : ℕ} (wm : ℤ → BitVec w) : ℤ := (wm 0).toInt

end SparseLowFactors.BoundedDeg


