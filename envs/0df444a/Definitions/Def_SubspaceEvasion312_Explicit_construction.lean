-- Prove2me | Definitions.Def_SubspaceEvasion312_Explicit_construction
-- name    : SubspaceEvasion312_Explicit_construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:56.343442+00:00
-- url     : https://prove2.me/theorems/79cfc63e-67d8-472e-92d2-9205e39c0152
-- title:
--   Global graph assemblies and the full fixed-field target
-- statement:
--   A raw assembly records dimensions $s,b,M,k$, an additive code $C\le(F^s)^M$, a linear map $E:F^k\to(F^s)^M$, and a local map $f:F^s\to F^b$. It has no correctness or efficiency fields. Its constructed point is exactly the coordinate concatenation
--
--   $$x\longmapsto(x,f(E(x)_1),\ldots,f(E(x)_M))\in F^N.$$
--
--   Validity asserts positive block dimensions and length, $N=k+bM$, $k=N-bM$, and the dimension-correct encoder conditions. The constructed set is the range of this point map. Its indexed bijection uses the canonical base-$q$ digits of an integer index and one fixed ordering of the field.
--
--   Define $\ell_A=\lceil16r^2/\varepsilon\rceil$, $\ell_B=\lceil256r(1+\log_2(r/\varepsilon))/\varepsilon\rceil$, and $L(r,\varepsilon)=\min(2\ell_A,2\ell_B)$. The fixed-field target demands actual assemblies for every sufficiently large $N$, with a fixed conditional-expectation local map, an appropriate zero-error list-recoverable code, and fixed indexing and membership programs. Both programs have charged time and natural-register bounds $C(N+1)^h$.
--
--   A fixed rational $\eta\in(3\varepsilon/4,\varepsilon)$ determines $M=\lfloor\eta N/b\rfloor$; the guaranteed density still uses the original real $\varepsilon$. The set has exactly $q^k$ points and at least $q^{(1-\varepsilon)N}$ points. The linear target uses rank $r$; its affine version uses the linear construction at rank $r+1$. These are conclusions of the goal, not assumed properties of input data.
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), Theorem 24 and proof, with Definition 3 affine comparison, printed p. 12 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf; PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc; affine comparison printed p. 2 (PDF p. 3)

import Definitions.Def_SubspaceEvasion312_Explicit_local_search

noncomputable section

namespace SubspaceEvasion312.Explicit
open scoped BigOperators ENNReal

/-- A raw description, with no evasiveness, dimension, correctness or cost fields. -/
structure Assembly (F : Type) [Field F] (N : ℕ) where
  s : ℕ
  b : ℕ
  m : ℕ
  k : ℕ
  code : Code F s m
  encoder : Vec F k →ₗ[F] Blocks F s m
  localMap : Vec F s → Vec F b

/-- Reindexing the actual graph into its N coordinates; Valid supplies the length equality. -/
def Assembly.point {F : Type} [Field F] {N : ℕ} (D : Assembly F N)
    (x : Vec F D.k) : Vec F N :=
  fun i => (vectorData x ++ blockData (compose D.encoder D.localMap x)).getD i 0

def Assembly.set {F : Type} [Field F] {N : ℕ} (D : Assembly F N) : Set (Vec F N) :=
  Set.range D.point

def Assembly.Valid {F : Type} [Field F] {N : ℕ} (D : Assembly F N) : Prop :=
  0 < D.s ∧ 0 < D.b ∧ 0 < D.m ∧ N = D.k + D.b * D.m ∧
    D.k = N - D.b * D.m ∧ IsEncoder D.code D.encoder

/-- Canonical least-significant-first base-q digits in the fixed field alphabet. -/
def indexVector {F : Type} [Field F] [Fintype F]
    (alphabet : Fin (Fintype.card F) ≃ F) {k : ℕ}
    (i : Fin ((Fintype.card F)^k)) : Vec F k :=
  fun j => alphabet ⟨(i.val / (Fintype.card F)^j.val) % Fintype.card F,
    Nat.mod_lt _ Fintype.card_pos⟩

/-- A true indexed bijection with the specified base-q digits, not an arbitrary reindexing. -/
def Assembly.Indexed {F : Type} [Field F] [Fintype F] {N : ℕ}
    (D : Assembly F N) (alphabet : Fin (Fintype.card F) ≃ F) : Prop :=
  ∃ index : Fin ((Fintype.card F) ^ D.k) ≃ D.set,
    ∀ i, (index i).val = D.point (indexVector alphabet i)

/-- Uniform in N; no N-indexed program or uncharged preprocessing advice. -/
def GlobalAlgorithms {F : Type} [Field F] (D : ∀ N, Assembly F N)
    (index member : Program F) (C degree N₀ : ℕ) : Prop := by
  classical
  exact ∀ N ≥ N₀,
    (∀ x, RunsWithin index [N] (vectorData x)
      (C * (N + 1) ^ degree) (C * (N + 1) ^ degree) (vectorData ((D N).point x))) ∧
    (∀ y : Vec F N, RunsWithin member [N] (vectorData y)
      (C * (N + 1) ^ degree) (C * (N + 1) ^ degree)
      [if y ∈ (D N).set then 1 else 0])

def quadraticList (r : ℕ) (ε : ℝ) : ℕ := ⌈16 * (r : ℝ)^2 / ε⌉₊
def logarithmicList (r : ℕ) (ε : ℝ) : ℕ :=
  ⌈256 * (r : ℝ) * (1 + log₂ (r / ε)) / ε⌉₊
def intersectionBound (r : ℕ) (ε : ℝ) : ℕ :=
  min (2 * quadraticList r ε) (2 * logarithmicList r ε)
def asymptoticShape (r : ℕ) (ε : ℝ) : ℝ :=
  min ((r : ℝ)^2 / ε) ((r : ℝ) * log₂ (r / ε) / ε)

/-- All algebraic and algorithmic assertions are conclusions in the goal.
The rational eta is finite advice for fixed real epsilon; it is not an exact-real input.
The local map is the actual conditional-expectation map, not an unknown evasive set. -/
def FixedFieldConstruction {F : Type} [Field F] [Fintype F]
    (r : ℕ) (ε : ℝ) (degree : ℕ) (affine : Bool) : Prop :=
  ∃ (η : ℚ) (s b d N₀ C : ℕ) (alphabet : Fin (Fintype.card F) ≃ F)
    (D : ∀ N, Assembly F N) (index member : Program F),
    3 * ε / 4 < (η : ℝ) ∧ (η : ℝ) < ε ∧
    0 < s ∧ 0 < b ∧ 0 < d ∧ 0 < N₀ ∧ 0 < C ∧
    GlobalAlgorithms D index member C degree N₀ ∧
    ∀ N ≥ N₀,
      let A := D N
      A.Valid ∧ A.s = s ∧ A.b = b ∧
      A.m = ⌊(η : ℝ) * N / b⌋₊ ∧
      A.localMap = localFunction (List.ofFn alphabet) A.s A.b r d ∧
      (s + b + d) * r < b * d ∧
      2 * (d - 1) ≤ intersectionBound r ε ∧
      ListRecoverable A.code r 0 (d - 1) (2 * (d - 1)) ∧
      A.Indexed alphabet ∧ A.set.Finite ∧ A.set.ncard = (Fintype.card F) ^ A.k ∧
      (Fintype.card F : ℝ) ^ ((1 - ε) * N) ≤ (A.set.ncard : ℝ) ∧
      Evasive (F := F) A.set r (intersectionBound r ε) ∧
      (affine = true → AffineEvasive (F := F) A.set (r - 1) (intersectionBound r ε))

end SubspaceEvasion312.Explicit


