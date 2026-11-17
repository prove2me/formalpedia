-- Prove2me | Definitions.Def_PathCount2k_Supplement_CircuitAlgorithm
-- name    : PathCount2k_Supplement_CircuitAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:21:29.292201+00:00
-- url     : https://prove2.me/theorems/8f9f38fb-fb72-4bf7-a6a8-c58308923e8c
-- title:
--   §4 — the multilinear-monomial counting algorithm with Clifford-algebra exterior products as a charged program
-- statement:
--   This definition writes out the algorithm of §4 (pp.27–34) that proves Theorem 1.3, as a program whose arithmetic operations are counted. It is parametrized by the cost $\mathrm{mmCost}(r,A,B)$ of multiplying two real $r\times r$ matrices (the product used is the exact product $AB$).
--
--   1. **Preprocessing** (§4.1). Mark the gates used by the output, decide which gates compute the zero polynomial (no cancellation occurs in a monotone circuit), and relabel the occurring variables. The zero polynomial returns $0$; $k=1$ returns $f(1,\dots,1)$; $k$ larger than the number of occurring variables returns $0$.
--   2. **Tags** (Definition 4.3, Lemma 4.2). The tag universe $J$ consists of the pairs (sum wire $e=(v,u)$, position $p$) with $1\le p\le k-d_v+1$, ordered by position, then gates (every gate before its inputs), then wire; $L=|J|$ and $D=\max\{1,L\}$.
--   3. **One trial.** Each occurring variable gets a vector $g_i\in\mathbb Z^k$ with independent $\xi$-distributed coordinates (Definition 2.15); each tag gets a uniform signed permutation $O_{e,p}$ of dimension $D$ (Fisher–Yates with rejection-sampled uniform choices, then $D$ fair signs). The gate–position states of Definition 4.6 are $F_{v,p}=g_i\otimes I_D$ at a leaf, $F_{v,p}=\sum_e\sqrt{a_e}\,(e_\emptyset\otimes O_{e,p})\star F_{u,p}$ at a sum gate, and $F_{v,p}=F_{u,p}\star F_{w,p+d_u}$ at a product gate; $z_0=[F_{o,1}]_{[k]}\beta$ with $\beta=(1,0,\dots,0)^{\top}$.
--   4. **Products.** $F\star G$ is computed by $D^3$ scalar exterior products $\widetilde{(F\star G)}_{ac}=\sum_b\tilde F_{ab}\wedge\tilde G_{bc}$ (proof of Lemma 4.7). Each scalar exterior product is computed through Clifford-algebra multiplication: inputs are split by degree, mapped to real matrices of order $2^{\lceil k/2\rceil}$ by an explicit faithful representation (butterfly transforms, $2^kk^{O(1)}$ operations), multiplied with cost $\mathrm{mmCost}$, mapped back, and only the output subsets whose size is the sum of the input degrees are kept.
--   5. **Amplification** (§4.8). $R=\lceil24K_k\varepsilon^{-2}\rceil$, $q=2\lceil\log_2(2/\delta)\rceil+1$, $r=Rq(kn+L(D-1))$ rejection requests with one global budget of $8r$ attempts (Lemma 4.10), returning $0$ if it is exhausted; $A_j=\sum_\ell\|z_{0,j,\ell}\|^2$; output $\mathrm{median}(A_1,\dots,A_q)/(R\,k!)$ with a linear-time median over $\mathbb R$.
--
--   The random-bit budget is $8r\max\{4,\lceil\log_2D\rceil\}+RqLD$ in the main case and $0$ otherwise.
--
--   **Formalization Note** Written in the cost monad `CapacitatedAssort.General.Work` in the paper's weighted arithmetic model: every arithmetic operation, comparison, square root of a weight, loop step, sampling attempt and bit read is charged where its value is formed. The Clifford representation uses generators $Z^{\otimes p}\otimes X\otimes I^{\otimes(m-p-1)}$ and $Z^{\otimes p}\otimes J\otimes I^{\otimes(m-p-1)}$ with $X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $J=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$, $Z=\mathrm{diag}(1,-1)$, $m=\lceil k/2\rceil$. Positions are 0-based. Within a trial the $kn$ vector coordinates are drawn first, then the tags in the order of Lemma 4.2.
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), §4.1–§4.8, pp.27–34: Definitions 4.3–4.6 pp.29–31, Lemma 4.7 p.32, Lemma 4.10 p.33, the complete algorithm p.34

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_PathCount2k_Exterior
import Definitions.Def_PathCount2k_Gaussian
import Definitions.Def_PathCount2k_Algorithm
import Definitions.Def_PathCount2k_Supplement_Circuit

open CapacitatedAssort.General

namespace PathCount2k.Supplement

/-! # The algorithm of Theorem 1.3 (§4) as a charged program on a fair-bit tape

Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026),
§4.1–§4.8, pp.27–34.

**Formalization Note.**
1. *Cost model.* The published monad `CapacitatedAssort.General.Work`, in the paper's weighted
   arithmetic model (p.32: "Square roots of the weights are computed once and reused"; p.33: "For
   arbitrary weights, the arithmetic model in Theorem 1.3 applies"): each arithmetic operation,
   comparison, square root, loop step and sampling attempt is charged at the site where its value is
   formed; a charged step returns a pure expression whose naive evaluation performs exactly the
   charged operations.
2. *Matrix multiplication* is a parameter: the cost `mmCost r A B` of multiplying two real `r × r`
   matrices; the product returned is `A * B` (a correct routine). Theorem 1.3's "`ω` … any exponent
   for which square matrices of order `r` can be multiplied in `O(r^ω)` arithmetic operations" is the
   hypothesis `mmCost r A B ≤ C_mm r^ω` in the theorem.
3. *Scalar exterior multiplication* (Lemma 4.7, p.32: "Clifford-algebra multiplication gives
   `T∧(k) = 2^{ωk/2}k^{O(1)}`; see Włodarczyk [Wło19, Theorem 5 and Appendix B] and … Brand, Dell,
   and Husfeldt [BDH18, Section 2.3]. The reduction groups inputs by degree and uses Clifford
   multiplication, retaining only output subsets whose cardinality equals the sum of the input
   degrees. … Clifford multiplication reduces to real matrix multiplication of order `2^{k/2+O(1)}`,
   with `2^k k^{O(1)}` transformation work."). Concretely: with `m = ⌈k/2⌉` and `r = 2^m`, the
   generators `e_{2p} ↦ Z^{⊗p} ⊗ X ⊗ I^{⊗(m−p−1)}`, `e_{2p+1} ↦ Z^{⊗p} ⊗ J ⊗ I^{⊗(m−p−1)}` with
   `X = [[0,1],[1,0]]`, `J = [[0,1],[−1,0]]`, `Z = diag(1,−1)` give an injective algebra map `ρ` from
   the real Clifford algebra with `e_{2p}² = 1`, `e_{2p+1}² = −1` (basis `e_S` = increasing products)
   into `r × r` real matrices. For disjoint `A, B`, `e_A e_B = (−1)^{inv(A,B)} e_{A∪B}`; otherwise the
   product has smaller degree. So `a ∧ b = ∑_{p,q} ⟨ρ⁻¹(ρ(a_p) ρ(b_q))⟩_{p+q}`. The maps `ρ` and
   `ρ⁻¹` are computed by `m` butterfly stages per flip pattern (`toMat`, `fromMat`), `O(k 2^k)`
   operations; one Clifford product costs two `toMat`, one matrix multiplication (`mmCost`) and one
   `fromMat`.
4. *Matrix-valued products* (Lemma 4.7's proof): `(F ⋆ G)~_{ac} = ∑_b F̃_{ab} ∧ G̃_{bc}`, `D³` scalar
   exterior products and `O(2^k D³)` additions (`starFast`).
5. *Sampling* (§4.8, Lemma 4.10): one global budget of `8r` rejection attempts,
   `r = Rq(kn + L(D − 1))` requests: the four-bit sampler of `ξ` (§2.9) for the variable vectors and,
   for each tag, the Fisher–Yates shuffle "for `j = D, D−1, …, 2`, swap its `j`th entry with an
   independently uniform entry among the first `j`", a uniform choice in `[j]` reading `⌈log₂ j⌉`
   bits most significant first and rejecting values `≥ j`; then `D` sign bits per tag (`true ↦ −1`).
   All bits come from one tape read left to right. On exhaustion the program returns `0`. Within a
   trial: first the `k·n` vector coordinates (`g_i(j)` is draw `i·k + j`, as `PathCount2k.vecOf`),
   then the tags in the order of Lemma 4.2. One charge per sampling attempt plus one per bit read.
6. *Positions* are 0-based: the paper's state `(v, p)` is `(v, p − 1)`.
7. *Amplification* (§4.8): `R = ⌈24 K_k ε⁻²⌉`, `q = 2⌈log₂(2/δ)⌉ + 1`, linear-time median over ℝ
   (`selectR`, median of medians), output `median(A₁, …, A_q)/(R k!)`. -/

/-! ## Preprocessing (§4.1, Definition 4.3, Lemma 4.2) -/

/-- The input gates of a gate. -/
def Gate.inputs {n g : ℕ} : Gate n g → List (Fin g)
  | .leaf _ => []
  | .sum ws => ws.map (·.1)
  | .prod u w => [u, w]

/-- Gates used by the output (§4.1, p.28: "Delete gates not used by the output"), marked from the
output downwards. -/
def Circuit.used {n : ℕ} (C : Circuit n) : Fin C.size → Bool :=
  (List.finRange C.size).reverse.foldl
    (fun U v => if U v then fun u => U u || (C.gate v).inputs.contains u else U)
    fun u => decide (u = C.out)

/-- Whether `f_v ≠ 0`: by monotonicity (nonnegative weights) there is no cancellation, so a sum
gate is nonzero iff some wire of positive weight leads to a nonzero gate, a product iff both inputs
are nonzero (Lemma 4.1's proof: "Monotonicity allows zero components to be recognized"). -/
noncomputable def Circuit.nz {n : ℕ} (C : Circuit n) : Fin C.size → Bool :=
  (List.finRange C.size).foldl
    (fun Z v => Function.update Z v (match C.gate v with
      | .leaf _ => true
      | .sum ws => ws.any fun e => decide (0 < e.2) && Z e.1
      | .prod u w => Z u && Z w))
    fun _ => false

/-- The occurring variables (labels of used leaves), in order of first occurrence by gate number;
the relabelling `x_{vars[i]} ↦ x_i` of §4.1 ("relabel the occurring variables as `x₁, …, x_n`, so
`n ≤ s`"). -/
def Circuit.vars {n : ℕ} (C : Circuit n) : List (Fin n) :=
  (List.finRange C.size).foldl
    (fun acc v => if C.used v then
      (match C.gate v with
        | .leaf i => if i ∈ acc then acc else acc ++ [i]
        | _ => acc) else acc) []

/-- The value `f(1, …, 1)` (§4.1: "For `k = 1`, evaluating at `x₁ = ⋯ = x_n = 1` gives the answer
exactly"). -/
noncomputable def Circuit.valOnes {n : ℕ} (C : Circuit n) : ℝ :=
  ((List.finRange C.size).foldl
    (fun F v => Function.update F v (match C.gate v with
      | .leaf _ => 1
      | .sum ws => (ws.map fun e => e.2 * F e.1).sum
      | .prod u w => F u * F w))
    (fun _ => (0 : ℝ))) C.out

/-- **The tag universe `J` in the order of Lemma 4.2** (Definition 4.3, p.29: "The tag universe `J`
consists of all pairs `(e, p)` such that `e = (v, u)` is a sum wire and `1 ≤ p ≤ k − d_v + 1`";
Lemma 4.2's proof: "Order tags first by increasing position, then by this order of their sum gates
[a topological order placing every gate before its inputs], and finally by wire identity"). A tag
is `(v, w, p)`: wire number `w` of the used sum gate `v`, 0-based position `p` with
`p + d_v ≤ k`. Gates are visited by decreasing number (every gate before its inputs). -/
def Circuit.tags {n : ℕ} (C : Circuit n) : List (Fin C.size × ℕ × ℕ) :=
  let k := C.deg C.out
  (List.range k).flatMap fun p => (List.finRange C.size).reverse.flatMap fun v =>
    if C.used v ∧ p + C.deg v ≤ k then
      (match C.gate v with
        | .sum ws => (List.range ws.length).map fun w => (v, w, p)
        | _ => [])
    else []

/-- `R = ⌈24 K_k ε⁻²⌉`, §4.8 step 2, p.34. -/
noncomputable def paramR24 (k : ℕ) (ε : ℝ) : ℕ := ⌈24 * PathCount2k.Kk k / ε ^ 2⌉₊

/-- Whether the main branch runs (not the zero polynomial, `k ≠ 1`, `k ≤ n` after relabelling;
§4.8 step 1). -/
noncomputable def Circuit.main {n : ℕ} (C : Circuit n) : Prop :=
  C.nz C.out = true ∧ C.deg C.out ≠ 1 ∧ C.deg C.out ≤ C.vars.length

/-- **The random-bit budget** of §4.8, p.34: "The sampler uses at most
`8r max{4, ⌈log₂ D⌉} + RqLD` fair random bits", with `r = Rq(kn + L(D − 1))`, `n` the number of
occurring variables, `L = |J|`, `D = max{1, L}`; `0` in the exactly answered cases. -/
noncomputable def circBits {n : ℕ} (C : Circuit n) (ε δ : ℝ) : ℕ :=
  open Classical in
  let k := C.deg C.out
  let n' := C.vars.length
  let L := C.tags.length
  let D := max 1 L
  let R := paramR24 k ε
  let q := PathCount2k.paramq δ
  if C.main then 8 * (R * q * (k * n' + L * (D - 1))) * max 4 (Nat.clog 2 D) + R * q * L * D
  else 0

/-! ## Clifford-algebra exterior multiplication through matrix multiplication -/

/-- `m = ⌈k/2⌉`; the matrices have order `2^m`. -/
def half (k : ℕ) : ℕ := (k + 1) / 2

/-- Whether generator `i` (`0 ≤ i < 2m`) belongs to the basis set with flip bits `f` and choice bits
`y`: in pair `p = ⌊i/2⌋`, flip bit `0` means `∅` (`y_p = 0`) or `{2p, 2p+1}` (`y_p = 1`), flip bit `1`
means `{2p}` (`y_p = 0`) or `{2p+1}` (`y_p = 1`). -/
def memFY (f y i : ℕ) : Bool :=
  if f.testBit (i / 2) then (i % 2 == 1) == y.testBit (i / 2) else y.testBit (i / 2)

/-- The set is inside `Fin k` (for odd `k`, the generator `k` of the last pair is excluded). -/
def validFY (k y : ℕ) : Bool := k % 2 == 0 || !(y.testBit (half k - 1))

/-- The subset of `Fin k` with flip bits `f` and choice bits `y`. -/
def setFY (k f y : ℕ) : Finset (Fin k) := Finset.univ.filter fun i => memFY f y i.val

/-- Whether the natural number `g` is (the value of) an element of `S`. -/
def memN {k : ℕ} (S : Finset (Fin k)) (g : ℕ) : Bool := decide (∃ i ∈ S, i.val = g)

/-- The flip bits of `S`: bit `p` is `[2p ∈ S] xor [2p+1 ∈ S]`. -/
def fOf {k : ℕ} (S : Finset (Fin k)) : ℕ :=
  ∑ p ∈ Finset.range (half k), if xor (memN S (2 * p)) (memN S (2 * p + 1)) then 2 ^ p else 0

/-- The choice bits of `S`: bit `p` is `[2p+1 ∈ S]` if flip bit `p` is set, else `[2p ∈ S]`. -/
def yOf {k : ℕ} (S : Finset (Fin k)) : ℕ :=
  ∑ p ∈ Finset.range (half k),
    if xor (memN S (2 * p)) (memN S (2 * p + 1)) then (if memN S (2 * p + 1) then 2 ^ p else 0)
    else (if memN S (2 * p) then 2 ^ p else 0)

/-- The sign `∏_p (−1)^{q_p(f)·col_p}` contributed by the `Z` factors on the right
(`q_p(f)` = number of flip bits of `f` above `p`). -/
def sgn {K : Type} [Field K] (m f col : ℕ) : K :=
  (-1 : K) ^ (∑ p ∈ Finset.range m,
    (col.testBit p).toNat * ∑ p' ∈ Finset.Ioo p m, (f.testBit p').toNat)

/-- One forward butterfly stage on bit `p` (choice bit `y_p` ↦ row bit `row_p`) with kernel
`[[1,−1],[1,1]]` (flip bit `0`) or `[[1,1],[1,−1]]` (flip bit `1`). -/
def stageF {K : Type} [Field K] (fb : Bool) (p : ℕ) (w : ℕ → K) : ℕ → K := fun x =>
  if x.testBit p then
    (let a := w (x - 2 ^ p); let b := w x; if fb then a - b else a + b)
  else
    (let a := w x; let b := w (x + 2 ^ p); if fb then a + b else a - b)

/-- One inverse butterfly stage on bit `p` (row bit ↦ choice bit), kernels
`½[[1,1],[−1,1]]` (flip bit `0`) and `½[[1,1],[1,−1]]` (flip bit `1`). -/
def stageI {K : Type} [Field K] (fb : Bool) (p : ℕ) (w : ℕ → K) : ℕ → K := fun x =>
  if x.testBit p then
    (let a := w (x - 2 ^ p); let b := w x; if fb then (a - b) / 2 else (b - a) / 2)
  else
    (let a := w x; let b := w (x + 2 ^ p); (a + b) / 2)

/-- **`ρ(x)`** for `x ∈ Λ(ℝ^k)` read as a Clifford element: scatter the coefficients by flip pattern
`f` and choice bits `y`, `m` butterfly stages for each `f`, then
`ρ(x)[i, i ⊕ f] = sgn(f, i ⊕ f) · u_f[i]`. Charges: scatter `r²(k + 2)`, `3r` per stage, assembly
`r²(m² + 2)`. -/
def toMat {K : Type} [Field K] (k : ℕ) (x : Finset (Fin k) → K) :
    Work (Matrix (Fin (2 ^ half k)) (Fin (2 ^ half k)) K) := do
  let m := half k
  let r := 2 ^ m
  charge (r * r * (k + 2))
  let mut W : ℕ → ℕ → K := fun f y => if validFY k y then x (setFY k f y) else 0
  for f in List.range r do
    for p in List.range m do
      charge (3 * r)
      let w := stageF (f.testBit p) p (W f)
      W := fun f' => if f' = f then w else W f'
  charge (r * r * (m * m + 2))
  return Matrix.of fun i j => sgn m (i.val ^^^ j.val) j.val * W (i.val ^^^ j.val) i.val

/-- **`ρ⁻¹(M)`**: undo the signs, `m` inverse butterfly stages per flip pattern, read the
coefficient of each `S ⊆ Fin k` at `(fOf S, yOf S)`. -/
def fromMat {K : Type} [Field K] (k : ℕ) (M : Matrix (Fin (2 ^ half k)) (Fin (2 ^ half k)) K) :
    Work (Finset (Fin k) → K) := do
  let m := half k
  let r := 2 ^ m
  charge (r * r * (m * m + 2))
  let mut W : ℕ → ℕ → K := fun f i =>
    if h : i < r ∧ i ^^^ f < r then sgn m f (i ^^^ f) * M ⟨i, h.1⟩ ⟨i ^^^ f, h.2⟩ else 0
  for f in List.range r do
    for p in List.range m do
      charge (3 * r)
      let w := stageI (f.testBit p) p (W f)
      W := fun f' => if f' = f then w else W f'
  charge (2 ^ k * (k + 2))
  return fun S => W (fOf S) (yOf S)

/-- One Clifford product `ρ⁻¹(ρ(x) ρ(y))`, the matrix product charged `mmCost`. -/
def cliff {K : Type} [Field K]
    (mmCost : (r : ℕ) → Matrix (Fin r) (Fin r) K → Matrix (Fin r) (Fin r) K → ℕ) (k : ℕ)
    (x y : Finset (Fin k) → K) : Work (Finset (Fin k) → K) := do
  let A ← toMat k x
  let B ← toMat k y
  charge (mmCost (2 ^ half k) A B)
  fromMat k (A * B)

/-- The homogeneous degree-`d` part. -/
def proj {K : Type} [Zero K] {k : ℕ} (d : ℕ) (x : Finset (Fin k) → K) : Finset (Fin k) → K :=
  fun S => if S.card = d then x S else 0

/-- **Scalar exterior product through Clifford multiplication**: `x ∧ y = ∑_{p+q ≤ k}
⟨x_p y_q⟩_{p+q}` ("groups inputs by degree … retaining only output subsets whose cardinality
equals the sum of the input degrees"). Charged `3·2^k + 1` per pair `(p, q)` for the projections
and the accumulation. -/
def wedgeFast {K : Type} [Field K]
    (mmCost : (r : ℕ) → Matrix (Fin r) (Fin r) K → Matrix (Fin r) (Fin r) K → ℕ)
    (k : ℕ) (x y : Finset (Fin k) → K) : Work (Finset (Fin k) → K) := do
  let mut out : Finset (Fin k) → K := fun _ => 0
  for p in List.range (k + 1) do
    for q in List.range (k + 1) do
      charge (3 * 2 ^ k + 1)
      if p + q ≤ k then
        let c ← cliff mmCost k (proj p x) (proj q y)
        out := out + proj (p + q) c
  return out

/-- A real matrix-valued exterior element with `D × D` coefficients (Definition 3.4 with auxiliary
dimension `D`, §4.4). -/
abbrev RExt (k D : ℕ) := Finset (Fin k) → Matrix (Fin D) (Fin D) ℝ

/-- **`F ⋆ G` by `D³` scalar exterior products** (Lemma 4.7's proof, p.32: "define the scalar
exterior element `F̃_{ab} = ∑_A (F_A)_{ab} e_A` … Then `(F ⋆ G)~_{ac} = ∑_{b=1}^D F̃_{ab} ∧ G̃_{bc}`.
Thus `D³` scalar exterior products and `O(2^k D³)` additions suffice"). -/
noncomputable def starFast (mmCost : (r : ℕ) → Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ → ℕ)
    {k D : ℕ} (F G : RExt k D) : Work (RExt k D) := do
  charge (2 * 2 ^ k * D ^ 2)
  let mut out : Fin D → Fin D → Finset (Fin k) → ℝ := fun _ _ _ => 0
  for a in List.finRange D do
    for c in List.finRange D do
      for b in List.finRange D do
        let w ← wedgeFast mmCost k (fun S => F S a b) (fun S => G S b c)
        charge (2 ^ k + 1)
        out := fun a' c' => if a' = a ∧ c' = c then out a c + w else out a' c'
  charge (2 ^ k * D ^ 2)
  return fun S => Matrix.of fun a c => out a c S

/-- Left multiplication by the signed permutation `O` with `O_{π(j), j} = σ_j` (Definition 4.4),
`D²` operations per coefficient matrix. -/
def applySP {D : ℕ} (π : Fin D → Fin D) (σ : Fin D → ℝ) (M : Matrix (Fin D) (Fin D) ℝ) :
    Matrix (Fin D) (Fin D) ℝ :=
  Matrix.of fun i c => ∑ j : Fin D, if π j = i then σ j * M j c else 0

/-! ## Sampling and selection -/

/-- The `nb` bits at cursor `pos`, most significant first, as a natural number. -/
def readBits (t : ℕ → Bool) (pos nb : ℕ) : ℕ :=
  ∑ i ∈ Finset.range nb, 2 ^ (nb - 1 - i) * (t (pos + i)).toNat

/-- One rejection-sampling request from the global attempt budget `B`: read `nb` bits, accept a
value `< j`. Returns the value (`none` when the budget is exhausted), the new cursor and the
remaining budget. -/
def rej (t : ℕ → Bool) (nb j : ℕ) : ℕ → ℕ → Option ℕ × ℕ × ℕ
  | 0, pos => (none, pos, 0)
  | B + 1, pos =>
      if readBits t pos nb < j then (some (readBits t pos nb), pos + nb, B)
      else rej t nb j B (pos + nb)

/-- Median-of-medians selection over ℝ (the base mission's `PathCount2k.select`, on real values),
charging every comparison. -/
noncomputable def selectR : ℕ → List ℝ → ℕ → Work ℝ
  | 0, _, _ => pure 0
  | fuel + 1, xs, i =>
      if xs.length ≤ 5 then do
        charge 10
        return (xs.insertionSort (· ≤ ·)).getD i 0
      else do
        let groups := xs.toChunks 5
        charge (10 * groups.length)
        let meds := groups.map fun gr => (gr.insertionSort (· ≤ ·)).getD (gr.length / 2) 0
        let piv ← selectR fuel meds (meds.length / 2)
        charge (2 * xs.length)
        let lo := xs.filter (· < piv)
        let eq := xs.filter (· = piv)
        let hi := xs.filter (piv < ·)
        if i < lo.length then selectR fuel lo i
        else if i < lo.length + eq.length then return piv
        else selectR fuel hi (i - lo.length - eq.length)

/-- The median (the `(⌊q/2⌋ + 1)`-th smallest) of a list of reals. -/
noncomputable def selectMedianR (xs : List ℝ) : Work ℝ := selectR (xs.length + 1) xs (xs.length / 2)

/-! ## The complete algorithm (§4.8) -/

/-- **The algorithm of Theorem 1.3** (§4.8, p.34) on a circuit `C` over `n` variables, with
matrix-multiplication cost `mmCost`, accuracy `ε`, `δ`, and fair-bit tape `b`.
1. "Handle the zero polynomial, `k = 1`, and `k > n` exactly. Otherwise construct the tag order and
   set `D = max{1, L}`." (Preprocessing of §4.1: used gates, nonzero gates, relabelled variables.)
2. "Set `R = ⌈24K_kε⁻²⌉` and `q = 2⌈log₂(2/δ)⌉ + 1`. … `r = Rq(kn + L(D − 1))`. Allow at most `8r`
   attempts in total and return zero if the budget is exhausted. In addition, generate `RqLD`
   independent sign bits."
3. "For each group `j ∈ [q]`, evaluate `R` trials using Definition 4.6 with finite vector
   coordinates. Accumulate `A_j = ∑_{ℓ=1}^R ‖z_{0,j,ℓ}‖²`." Definition 4.6: a leaf `x_i` has
   `F_{v,p} = g_i ⊗ I_D`; a sum gate `F_{v,p} = ∑_{e=(v,u)} √a_e (e_∅ ⊗ O_{e,p}) ⋆ F_{u,p}`; a
   product `v = u · w` has `F_{v,p} = F_{u,p} ⋆ F_{w,p+d_u}`; at the output
   `z = [F_{o,1}]_{[k]} β`, `β = (1, 0, …, 0)ᵀ`.
4. "Return `M̂ = median(A₁, …, A_q)/(R k!)`."
The output is `((countMono mmCost C ε δ b).run 0).1`, the operation count
`((countMono mmCost C ε δ b).run 0).2`. -/
noncomputable def countMono
    (mmCost : (r : ℕ) → Matrix (Fin r) (Fin r) ℝ → Matrix (Fin r) (Fin r) ℝ → ℕ)
    {n : ℕ} (C : Circuit n) (ε δ : ℝ) (b : Fin (circBits C ε δ) → Bool) : Work ℝ := do
  -- preprocessing: used gates, nonzero gates, occurring variables
  charge (2 * C.sizeS + 2 + C.size * (C.size + 1))
  let k := C.deg C.out
  charge 1
  if C.nz C.out = false then return 0
  charge 1
  if k = 1 then
    charge (C.sizeS + 1)
    return C.valOnes
  let n' := C.vars.length
  charge 1
  if n' < k then return 0
  -- tags, D, square roots of the weights
  let tags := C.tags
  charge (k * (C.sizeS + 1))
  let L := tags.length
  let D := max 1 L
  charge 2
  charge C.sizeS
  -- parameters
  let R := paramR24 k ε
  charge (2 * R + 4)
  let r := PathCount2k.paramr δ
  charge (2 * r + 4)
  let q := 2 * r + 1
  charge 8
  let budget := 8 * (R * q * (k * n' + L * (D - 1)))
  charge 2
  let t : ℕ → Bool := fun i => if h' : i < circBits C ε δ then b ⟨i, h'⟩ else false
  let mut pos := 0
  let mut B := budget
  let mut sums : List ℝ := []
  for _j in List.range q do
    charge 1
    let mut acc : ℝ := 0
    for _l in List.range R do
      -- variable vectors
      let mut gx : List ℤ := []
      for _ in List.range (k * n') do
        let res := rej t 4 12 B pos
        charge (5 * (B - res.2.2) + 1)
        pos := res.2.1
        B := res.2.2
        match res.1 with
        | none => return 0
        | some u => gx := gx ++ [PathCount2k.xiDecode u]
      let g : Fin n' → Fin k → ℤ := PathCount2k.vecOf n' k gx
      -- signed permutations, one per tag, in the order of Lemma 4.2
      let mut perms : List ((Fin D → Fin D) × (Fin D → ℝ)) := []
      for _ in List.range L do
        let mut arr : Fin D → Fin D := id
        for j' in List.range (D - 1) do
          let j := D - j'
          let nb := Nat.clog 2 j
          let res := rej t nb j B pos
          charge ((nb + 1) * (B - res.2.2) + 1)
          pos := res.2.1
          B := res.2.2
          match res.1 with
          | none => return 0
          | some u =>
              charge 3
              if hu : u < D ∧ j - 1 < D then
                let a := arr ⟨j - 1, hu.2⟩
                let a' := arr ⟨u, hu.1⟩
                arr := fun x => if x.val = j - 1 then a' else if x.val = u then a else arr x
        let mut sg : Fin D → ℝ := fun _ => 1
        for i in List.finRange D do
          charge 1
          let bit := t pos
          sg := fun x => if x = i then (if bit then -1 else 1) else sg x
          pos := pos + 1
        perms := perms ++ [(arr, sg)]
      -- gate–position states (Definition 4.6), inputs before their gates
      let mut St : Fin C.size → ℕ → RExt k D := fun _ _ _ => 0
      for v in List.finRange C.size do
        charge 1
        if C.used v then
          for p in List.range (k + 1 - C.deg v) do
            charge 1
            match C.gate v with
            | .leaf i =>
                charge (2 ^ k * D ^ 2 + k * D + n')
                let idx := C.vars.idxOf i
                let gi : Fin k → ℤ := fun j => if h : idx < n' then g ⟨idx, h⟩ j else 0
                let Fv : RExt k D := fun A => ∑ j : Fin k, if A = {j} then (gi j : ℝ) • 1 else 0
                St := fun v' p' => if v' = v ∧ p' = p then Fv else St v' p'
            | .sum ws =>
                let mut Fv : RExt k D := fun _ => 0
                for w in List.range ws.length do
                  match ws[w]? with
                  | none => pure ()
                  | some e =>
                      charge (2 * 2 ^ k * D ^ 2 + L + 2)
                      let O := perms.getD (tags.idxOf (v, w, p)) (id, fun _ => 1)
                      let Fu := St e.1 p
                      Fv := Fv + fun A => Real.sqrt e.2 • applySP O.1 O.2 (Fu A)
                St := fun v' p' => if v' = v ∧ p' = p then Fv else St v' p'
            | .prod u w =>
                let Fv ← starFast mmCost (St u p) (St w (p + C.deg u))
                St := fun v' p' => if v' = v ∧ p' = p then Fv else St v' p'
      -- z = [F_{o,1}]_{[k]} β and ‖z‖²
      charge (2 * D + 1)
      if hD : 0 < D then
        acc := acc + ∑ a : Fin D, (St C.out 0 Finset.univ a ⟨0, hD⟩) ^ 2
    sums := acc :: sums
  let med ← selectMedianR sums
  charge (k + 2)
  return med / ((R : ℝ) * (Nat.factorial k : ℝ))

end PathCount2k.Supplement


