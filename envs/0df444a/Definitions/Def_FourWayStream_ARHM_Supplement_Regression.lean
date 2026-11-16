-- Prove2me | Definitions.Def_FourWayStream_ARHM_Supplement_Regression
-- name    : FourWayStream_ARHM_Supplement_Regression
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:57:56.153544+00:00
-- url     : https://prove2.me/theorems/d442f626-37cd-4486-9f58-34629faaf717
-- title:
--   Definition 5.17 and the hard family of p.26 — repeated regression sampling $\mathrm{RS}_{N,m}(B)$, pseudoinverse sampling, $U_M$ and $B_k=U_{F_k}^\top$
-- statement:
--   **Least-squares sampling.** For a real $N\times|\iota|$ matrix $B$, $B^+$ is its Moore–Penrose pseudoinverse, the unique matrix $X$ with $BXB=B$, $XBX=X$ and $BX$, $XB$ symmetric. For $y\in\mathbb R^N$ the **length-square distribution** of the least-squares solution is
--   $$p_{B,y}(J)=\frac{|(B^+y)_J|^2}{\|B^+y\|^2}\qquad(J\in\iota).$$
--
--   **The hard family.** For a perfect matching $M$ of $[N]$ and an orientation $e=\{u,v\}\mapsto(u,v)$ of its pairs, $U_M$ has two rows per pair,
--   $$(U_My)_{(e,0)}=\frac{y_u+y_v}{\sqrt2},\qquad (U_My)_{(e,1)}=\frac{y_u-y_v}{\sqrt2}.$$
--   For a one-factorization $F=\{F_1,\dots,F_{N-1}\}$ of $K_N$, $B_k=U_{F_k}^\top$ and $B_F=\{B_1,\dots,B_{N-1}\}$. The promised response vectors are the flat vectors $y_j=(-1)^{x_j}/\sqrt N$, $x\in\{0,1\}^N$.
--
--   **The stream $\mathrm{RS}_{N,m}(B)$.** It consists of the $NL$ labeled observations $(j,y_j,\ell)$, $j\in[N]$, $\ell\in[L]$, and $m$ labeled requests $(t,k_t)$, each naming $B_{k_t}$; the labeled occurrences and the two orders (uniformly random; data-first, the observations in any order followed by the requests in list order) are those of ARHM. On request $t$ the algorithm writes an index $J_t$ before the next item.
--
--   **Algorithms.** A quantum streaming algorithm has memory $\mathbb C^d$, an initial density matrix and, for every stage and item, an instrument (a complete finite Kraus family indexed by the output); a classical one has $S$ states and stochastic transitions. Space is $\lceil\log_2 d\rceil$ qubits or $\lceil\log_2 S\rceil$ bits.
--
--   **Correctness (Definition 5.17).** For every promised $y$ and every request list, the law of the transcript $(J_1,\dots,J_m)$ over the order and the algorithm's randomness is within total variation distance $1/3$ of the product $p_{B_{k_1},y}\otimes\cdots\otimes p_{B_{k_m},y}$.
--
--   These objects let Theorem 5.19 state the ARHM lower bounds for a natural regression task.
--
--   **Formalization Note** The family is given by a common index type $\iota$ and column sets $\mathrm{Ix}(k)\subseteq\iota$; for $B_F$, $\iota$ is pairs $(e,b)$ and $\mathrm{Ix}(k)$ the pairs with $e\in F_k$ ($b=\mathsf{false}$ is the row $(e,0)$). An output outside $\mathrm{Ix}(k_t)$, or no output, has ideal probability $0$. Observation items carry the real $y_j$; the promise restricts it to flat vectors.
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §5.4.1, p.26, Definition 5.17 and the hard family before Lemma 5.18; Appendix A, p.43; §4.2, p.16

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream

set_option autoImplicit false

/-!
# Repeated regression sampling (Definition 5.17) and its Hidden Matching family

Nadezhda Voronova, *Four Ways to Stream: Exponential Separations from Random Order and Quantum
Memory*, STOC 2027 submission #1371 (October 2026): §5.4.1, Definition 5.17 and the hard family
before Lemma 5.18 (p.26); Appendix A (p.43); the space model of §4.2 (p.16).

* `pinv B` is the Moore–Penrose pseudoinverse (the unique matrix satisfying the four Penrose
  conditions), and `lsProb B y J = |(B⁺y)_J|² / ‖B⁺y‖²` is the length-square distribution of the
  least-squares solution.
* `hmU M ori` is the matrix `U_M` of the hard family: for every pair `e` of the perfect matching `M`,
  oriented as `ori e = (u, v)`, the rows `(e, 0)` and `(e, 1)` are `(y_u + y_v)/√2` and
  `(y_u − y_v)/√2`; `hmB F ori k = U_{F_k}ᵀ`. The rows are indexed by `rowSet M`, the pairs `(e, b)`
  with `e ∈ M`; the bit `b = false` is the row `(e, 0)`.
* The stream `RS_{N,m}(B)` has the labeled observations `(j, y_j, ℓ)` and the labeled requests
  `(t, k_t)`, at the same labeled occurrences (`Pos N m L`) and in the same orders as `ARHM`. An
  algorithm writes an output after every item; on a request item the output is the index `J_t`.
* Correctness (Definition 5.17): for every promised `y` and every request list, the law of the
  transcript `(J_1, …, J_m)` (the outputs at the `m` requests, listed by tag), over the order and the
  algorithm's randomness, is within total variation distance `1/3` of the product
  `p_{B_{k_1},y} ⊗ ⋯ ⊗ p_{B_{k_m},y}`.

Algorithms follow the reading of §4.2 recorded in the base mission (module
`FourWayStream_ARHM_Stream`): memory `C^d`, every item processed by a quantum instrument (finite
complete Kraus family indexed by the output and an auxiliary index), which may depend on the stage;
space `⌈log₂ d⌉`. Classical algorithms: `S` states, stochastic transitions, space `⌈log₂ S⌉`.
-/

noncomputable section
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-! ### Least-squares sampling -/

/-- The four Penrose conditions: `X` is the Moore–Penrose pseudoinverse of `B`. -/
def IsPseudoinverse {α β : Type*} [Fintype α] [Fintype β] (B : Matrix α β ℝ) (X : Matrix β α ℝ) :
    Prop :=
  B * X * B = B ∧ X * B * X = X ∧ (B * X)ᵀ = B * X ∧ (X * B)ᵀ = X * B

/-- `B⁺`, the Moore–Penrose pseudoinverse of `B`. It exists and is unique for every real matrix, so
the `else` branch is never taken. -/
def pinv {α β : Type*} [Fintype α] [Fintype β] (B : Matrix α β ℝ) : Matrix β α ℝ :=
  if h : ∃ X, IsPseudoinverse B X then h.choose else 0

/-- The length-square distribution of the least-squares solution `B⁺y` (§5.4.1, p.26):
`p_{B,y}(J) = |(B⁺y)_J|² / ‖B⁺y‖²` (Lean's `x / 0 = 0` when `B⁺y = 0`). -/
def lsProb {N : ℕ} {ι : Type*} [Fintype ι] (B : Matrix (Fin N) ι ℝ) (y : Fin N → ℝ) (J : ι) : ℝ :=
  ((pinv B).mulVec y J) ^ 2 / ∑ J', ((pinv B).mulVec y J') ^ 2

/-! ### The Hidden Matching family (p.26) -/

/-- An orientation of the pairs: `ori e = (u, v)` with `{u, v} = e` for every pair `e` that is not
a loop ("orient each pair `e = {u, v}` arbitrarily"). -/
def IsOrientation {N : ℕ} (ori : Sym2 (Fin N) → Fin N × Fin N) : Prop :=
  ∀ e : Sym2 (Fin N), ¬ e.IsDiag → s((ori e).1, (ori e).2) = e

/-- The row indices of `U_M`: the pairs `(e, b)` with `e ∈ M` (`b = false` is the row `(e, 0)`). -/
def rowSet {N : ℕ} (M : Finset (Sym2 (Fin N))) : Finset (Sym2 (Fin N) × Bool) :=
  Finset.univ.filter (fun p => p.1 ∈ M)

/-- `U_M` (p.26): `(U_M y)_{(e,0)} = (y_u + y_v)/√2` and `(U_M y)_{(e,1)} = (y_u − y_v)/√2`, where
`ori e = (u, v)`. -/
def hmU {N : ℕ} (M : Finset (Sym2 (Fin N))) (ori : Sym2 (Fin N) → Fin N × Fin N) :
    Matrix (rowSet M) (Fin N) ℝ :=
  fun p j =>
    (if j = (ori p.1.1).1 then 1 / Real.sqrt 2 else 0) +
      (if j = (ori p.1.1).2 then (if p.1.2 then -1 else 1) / Real.sqrt 2 else 0)

/-- `B_k = U_{F_k}ᵀ` (p.26). -/
def hmB {N : ℕ} (F : Fin (N - 1) → Finset (Sym2 (Fin N))) (ori : Sym2 (Fin N) → Fin N × Fin N)
    (k : Fin (N - 1)) : Matrix (Fin N) (rowSet (F k)) ℝ :=
  (hmU (F k) ori)ᵀ

/-- The promise (p.26): the flat vector `y_j = (−1)^{x_j}/√N` of `x ∈ {0,1}^N`. -/
def flatVec {N : ℕ} (x : Fin N → Bool) : Fin N → ℝ :=
  fun j => (if x j then -1 else 1) / Real.sqrt N

/-- The promised response vectors of the hard family: the flat vectors. -/
def flatPromise (N : ℕ) : Set (Fin N → ℝ) := Set.range (flatVec (N := N))

/-! ### The stream `RS_{N,m}(B)` -/

/-- The items of `RS_{N,m}(B)` with `L` copies (Definition 5.17): a labeled observation
`(j, y_j, ℓ)` and a labeled request `(t, k_t)`. -/
inductive RSItem (N m L : ℕ) where
  | obs (j : Fin N) (y : ℝ) (ℓ : Fin L)
  | request (t : Fin m) (k : Fin (N - 1))

/-- The tag of a request item. -/
def RSItem.tag {N m L : ℕ} : RSItem N m L → Option (Fin m)
  | .obs _ _ _ => none
  | .request t _ => some t

/-- The item carried by a labeled occurrence (the occurrences are those of `ARHM`). -/
def rsItemAt {N m L : ℕ} (y : Fin N → ℝ) (ks : Fin m → Fin (N - 1)) : Pos N m L → RSItem N m L
  | .inl p => .obs p.1 (y p.1) p.2
  | .inr t => .request t (ks t)

/-- The stream in the random-order arrival `σ`. -/
def rsRandomStream {N m L : ℕ} (y : Fin N → ℝ) (ks : Fin m → Fin (N - 1)) (σ : Arrival N m L) :
    Fin (N * L + m) → RSItem N m L :=
  fun i => rsItemAt y ks (σ i)

/-- The data-first stream: the `N L` observations in the order `τ`, then the `m` requests in list
order. -/
def rsDataFirstStream {N m L : ℕ} (y : Fin N → ℝ) (ks : Fin m → Fin (N - 1))
    (τ : Fin (N * L) ≃ Fin N × Fin L) : Fin (N * L + m) → RSItem N m L :=
  Fin.append (fun i => RSItem.obs (τ i).1 (y (τ i).1) (τ i).2) (fun t => RSItem.request t (ks t))

/-- A family `B = {B_1, …, B_{N−1}}` of matrices whose column (output) indices lie in a common type
`ι`: `B_k` has the columns `Ix k`. The ideal law of the answer to a request for `B_k`:
`p_{B_k,y}` on `Ix k`, and `0` elsewhere (no answer is never ideal). -/
def idealOut {N : ℕ} {ι : Type*} (Ix : Fin (N - 1) → Finset ι)
    (B : (k : Fin (N - 1)) → Matrix (Fin N) (Ix k) ℝ) (y : Fin N → ℝ) (k : Fin (N - 1)) :
    Option ι → ℝ
  | none => 0
  | some j => if h : j ∈ Ix k then lsProb (B k) y ⟨j, h⟩ else 0

/-- Total variation distance `½ Σ |P − Q|`. -/
def tvDist {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ := (1 / 2) * ∑ a, |P a - Q a|

/-! ### Streaming algorithms with outputs -/

/-- A quantum streaming algorithm on items `It` writing outputs `Out` (§4.2, read with arbitrary
channels): memory `C^d`, initial state `ρ0`, and for every stage and item an instrument with Kraus
operators `kraus s it o j` indexed by the output `o` and an auxiliary index `j`. -/
structure QIOAlg (It Out : Type) where
  d : ℕ
  ρ0 : Matrix (Fin d) (Fin d) ℂ
  r : ℕ
  kraus : ℕ → It → Out → Fin r → Matrix (Fin d) (Fin d) ℂ

namespace QIOAlg

variable {It Out : Type} [Fintype Out]

/-- `ρ0` is a density matrix and every instrument is complete. -/
def Valid (A : QIOAlg It Out) : Prop :=
  IsDensityMatrix A.ρ0 ∧ ∀ s it, IsKrausFamily (fun p : Out × Fin A.r => A.kraus s it p.1 p.2)

/-- Process `its 0, …, its (n−1)` at stages `0, …, n−1`, keeping at step `i` only the outputs in
`keep i` (unnormalized). -/
def run (A : QIOAlg It Out) {n : ℕ} (its : Fin n → It) (keep : Fin n → Out → Prop) :
    Matrix (Fin A.d) (Fin A.d) ℂ :=
  Fin.foldl n (fun ρ i => ∑ o, if keep i o then
    ∑ j, A.kraus i.val (its i) o j * ρ * (A.kraus i.val (its i) o j)ᴴ else 0) A.ρ0

/-- Space: `⌈log₂ d⌉` qubits. -/
def space (A : QIOAlg It Out) : ℕ := Nat.clog 2 A.d

end QIOAlg

/-- A classical randomized streaming algorithm on items `It` writing outputs `Out`: `S` states, an
initial distribution, and transitions `trans s it a (b, o)`. -/
structure CIOAlg (It Out : Type) where
  S : ℕ
  init : Fin S → ℝ
  trans : ℕ → It → Fin S → Fin S × Out → ℝ

namespace CIOAlg

variable {It Out : Type} [Fintype Out]

/-- `init` and every row of every transition are probability vectors. -/
def Valid (A : CIOAlg It Out) : Prop :=
  ((∀ a, 0 ≤ A.init a) ∧ ∑ a, A.init a = 1) ∧
    ∀ s it a, (∀ p, 0 ≤ A.trans s it a p) ∧ ∑ p, A.trans s it a p = 1

/-- The (unnormalized) state distribution after `its`, keeping at step `i` the outputs in `keep i`. -/
def run (A : CIOAlg It Out) {n : ℕ} (its : Fin n → It) (keep : Fin n → Out → Prop) :
    Fin A.S → ℝ :=
  Fin.foldl n (fun v i => fun b => ∑ a, v a * ∑ o, if keep i o then A.trans i.val (its i) a (b, o)
    else 0) A.init

/-- Space: `⌈log₂ S⌉` bits. -/
def space (A : CIOAlg It Out) : ℕ := Nat.clog 2 A.S

end CIOAlg

/-! ### Transcripts and correctness (Definition 5.17) -/

variable {N m L : ℕ} {ι : Type} [Fintype ι]

/-- Keep, at a request item with tag `t`, only the output `o t`. -/
def keepTranscript {n : ℕ} (str : Fin n → RSItem N m L) (o : Fin m → Option ι) :
    Fin n → Option ι → Prop :=
  fun i o' => match (str i).tag with
    | some t => o' = o t
    | none => True

/-- The probability that the quantum algorithm's transcript on the stream `str` is `o`. -/
def qTranscript (A : QIOAlg (RSItem N m L) (Option ι)) {n : ℕ} (str : Fin n → RSItem N m L)
    (o : Fin m → Option ι) : ℝ :=
  (A.run str (keepTranscript str o)).trace.re

/-- The probability that the classical algorithm's transcript on the stream `str` is `o`. -/
def cTranscript (A : CIOAlg (RSItem N m L) (Option ι)) {n : ℕ} (str : Fin n → RSItem N m L)
    (o : Fin m → Option ι) : ℝ :=
  ∑ b, A.run str (keepTranscript str o) b

/-- The ideal product law `p_{B_{k_1},y} ⊗ ⋯ ⊗ p_{B_{k_m},y}` of the transcript. -/
def idealTranscript (Ix : Fin (N - 1) → Finset ι) (B : (k : Fin (N - 1)) → Matrix (Fin N) (Ix k) ℝ)
    (y : Fin N → ℝ) (ks : Fin m → Fin (N - 1)) (o : Fin m → Option ι) : ℝ :=
  ∏ t, idealOut Ix B y (ks t) (o t)

/-- Definition 5.17, random order: for every promised `y` (in `Y`) and every request list, the law
of the transcript over the uniformly random arrival order and the measurements is within total
variation distance `η` of the ideal product law. -/
def QRSCorrectRand (A : QIOAlg (RSItem N m L) (Option ι)) (Ix : Fin (N - 1) → Finset ι)
    (B : (k : Fin (N - 1)) → Matrix (Fin N) (Ix k) ℝ) (Y : Set (Fin N → ℝ)) (η : ℝ) : Prop :=
  ∀ y ∈ Y, ∀ ks : Fin m → Fin (N - 1),
    tvDist (fun o => (∑ σ : Arrival N m L, qTranscript A (rsRandomStream y ks σ) o) /
        (Fintype.card (Arrival N m L) : ℝ)) (idealTranscript Ix B y ks) ≤ η

/-- Definition 5.17 in data-first order (Definition 5.2): for every promised `y`, every request list
and every order `τ` of the observations, the transcript law is within total variation distance `η`
of the ideal product law. -/
def QRSCorrectDataFirst (A : QIOAlg (RSItem N m L) (Option ι)) (Ix : Fin (N - 1) → Finset ι)
    (B : (k : Fin (N - 1)) → Matrix (Fin N) (Ix k) ℝ) (Y : Set (Fin N → ℝ)) (η : ℝ) : Prop :=
  ∀ y ∈ Y, ∀ (ks : Fin m → Fin (N - 1)) (τ : Fin (N * L) ≃ Fin N × Fin L),
    tvDist (qTranscript A (rsDataFirstStream y ks τ)) (idealTranscript Ix B y ks) ≤ η

/-- Definition 5.17 in random order, for a classical algorithm. -/
def CRSCorrectRand (A : CIOAlg (RSItem N m L) (Option ι)) (Ix : Fin (N - 1) → Finset ι)
    (B : (k : Fin (N - 1)) → Matrix (Fin N) (Ix k) ℝ) (Y : Set (Fin N → ℝ)) (η : ℝ) : Prop :=
  ∀ y ∈ Y, ∀ ks : Fin m → Fin (N - 1),
    tvDist (fun o => (∑ σ : Arrival N m L, cTranscript A (rsRandomStream y ks σ) o) /
        (Fintype.card (Arrival N m L) : ℝ)) (idealTranscript Ix B y ks) ≤ η

end FourWayStream.ARHM.Supplement


