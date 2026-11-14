-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Space
-- name    : BCFGJPSSV26_Greedy_Space
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:26.766198+00:00
-- url     : https://prove2.me/theorems/21deddca-41aa-453f-9ab9-5abe2717cd62
-- title:
--   BCFGJPSSV26.Greedy.Space — Spaces, parameters, atoms and profiles
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Space` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The setting of the analysis of [BCFGJPSSV26a, Section 5 and Appendices D and E]:
--
--   * **Spaces** (`BCFGJPSSV26.Greedy.Space`): a pseudometric with rational values on the clients
--     `Fin n` and the facilities `Fin m`; `X.d j i` is the distance from client `j` to facility `i`.
--   * **Parameters** (`BCFGJPSSV26.Greedy.Par`): `δ`, the paper's `ε` (here `P.ε`), the slack `η`,
--     the cap `K` of the profiles and the number `R` of phases. Phase `r` has time
--     `θ r = (1 + ε²)^r`; sequence `p` (counted from `0`) is of type 1 if `p` is even, of type 2 if
--     `p` is odd, and has time `θ (p / 2)` (`BCFGJPSSV26.Greedy.Par.θseq`).
--     `BCFGJPSSV26.Greedy.Par.Good` collects the conditions on them, and the lemmas after it the
--     inequalities the proofs use.
--   * **Atoms** (`BCFGJPSSV26.Greedy.Atom`): an opened facility, regular or a free copy at offset
--     `off` from its original (the paper's `u(ĩ)`); regular atoms have offset `0`. The analysis sees
--     an atom only through its pair `(fac, off)` (`BCFGJPSSV26.Greedy.Atom.pair`): in particular a free
--     copy at offset `0` and the regular facility have the same pair.
--   * **Profiles** (`BCFGJPSSV26.Greedy.profF`): the distance of client `j` to a set of pairs,
--     `min (K, min_{(i, u)} d j i + u)`, capped at `K`. A free atom at offset `K` is invisible
--     (`BCFGJPSSV26.Greedy.profF_insert_of_le`).
--
--   **Contents.** The module is published as a whole: 57 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Space`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Space.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Bid
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Space` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Spaces, parameters, atoms and profiles

The setting of the analysis of [BCFGJPSSV26a, Section 5 and Appendices D and E]:

* **Spaces** (`BCFGJPSSV26.Greedy.Space`): a pseudometric with rational values on the clients
  `Fin n` and the facilities `Fin m`; `X.d j i` is the distance from client `j` to facility `i`.
* **Parameters** (`BCFGJPSSV26.Greedy.Par`): `δ`, the paper's `ε` (here `P.ε`), the slack `η`,
  the cap `K` of the profiles and the number `R` of phases. Phase `r` has time
  `θ r = (1 + ε²)^r`; sequence `p` (counted from `0`) is of type 1 if `p` is even, of type 2 if
  `p` is odd, and has time `θ (p / 2)` (`BCFGJPSSV26.Greedy.Par.θseq`).
  `BCFGJPSSV26.Greedy.Par.Good` collects the conditions on them, and the lemmas after it the
  inequalities the proofs use.
* **Atoms** (`BCFGJPSSV26.Greedy.Atom`): an opened facility, regular or a free copy at offset
  `off` from its original (the paper's `u(ĩ)`); regular atoms have offset `0`. The analysis sees
  an atom only through its pair `(fac, off)` (`BCFGJPSSV26.Greedy.Atom.pair`): in particular a free
  copy at offset `0` and the regular facility have the same pair.
* **Profiles** (`BCFGJPSSV26.Greedy.profF`): the distance of client `j` to a set of pairs,
  `min (K, min_{(i, u)} d j i + u)`, capped at `K`. A free atom at offset `K` is invisible
  (`BCFGJPSSV26.Greedy.profF_insert_of_le`).
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

/-! ### Spaces -/

/-- A **space**: a pseudometric with rational values on the points `Fin n ⊕ Fin m`, the clients
`.inl j` and the facilities `.inr i`. -/
structure Space (n m : ℕ) where
  /-- The distance between two points. -/
  D : Fin n ⊕ Fin m → Fin n ⊕ Fin m → ℚ
  nonneg : ∀ a b, 0 ≤ D a b
  self : ∀ a, D a a = 0
  comm : ∀ a b, D a b = D b a
  triangle : ∀ a b c, D a c ≤ D a b + D b c

namespace Space

variable {n m : ℕ} (X : Space n m)

/-- The distance from client `j` to facility `i`. -/
def d (j : Fin n) (i : Fin m) : ℚ := X.D (.inl j) (.inr i)

/-- The distance between two facilities. -/
def dF (i i' : Fin m) : ℚ := X.D (.inr i) (.inr i')

/-- The distance between two clients. -/
def dC (j j' : Fin n) : ℚ := X.D (.inl j) (.inl j')

theorem d_nonneg (j : Fin n) (i : Fin m) : 0 ≤ X.d j i := X.nonneg _ _

theorem dC_comm (j j' : Fin n) : X.dC j j' = X.dC j' j := X.comm _ _

theorem dF_comm (i i' : Fin m) : X.dF i i' = X.dF i' i := X.comm _ _

/-- `d(j, i) ≤ d(j, j') + d(j', i)`. -/
theorem d_le_dC_add (j j' : Fin n) (i : Fin m) : X.d j i ≤ X.dC j j' + X.d j' i :=
  X.triangle _ _ _

/-- `d(j, i) ≤ d(j, i') + d(i', i)`. -/
theorem d_le_d_add_dF (j : Fin n) (i i' : Fin m) : X.d j i ≤ X.d j i' + X.dF i' i :=
  X.triangle _ _ _

/-- `d(i, i') ≤ d(j, i) + d(j, i')`. -/
theorem dF_le (j : Fin n) (i i' : Fin m) : X.dF i i' ≤ X.d j i + X.d j i' := by
  have h := X.triangle (.inr i) (.inl j) (.inr i')
  rw [X.comm (.inr i) (.inl j)] at h
  exact h

/-- `d(j, j') ≤ d(j, i) + d(j', i)`. -/
theorem dC_le (j j' : Fin n) (i : Fin m) : X.dC j j' ≤ X.d j i + X.d j' i := by
  have h := X.triangle (.inl j) (.inr i) (.inl j')
  rw [X.comm (.inr i) (.inl j')] at h
  exact h

end Space

/-! ### Parameters -/

/-- The **parameters** of the analysis: `δ`, the paper's `ε`, the slack `η` of
`(ν, η)`-openability, the cap `K` of the profiles, and the number `R` of phases. -/
structure Par where
  δ : ℚ
  ε : ℚ
  η : ℚ
  K : ℚ
  R : ℕ

namespace Par

variable (P : Par)

/-- The time of phase `r`: `θ r = (1 + ε²)^r`. -/
def θ (r : ℕ) : ℚ := (1 + P.ε ^ 2) ^ r

/-- The time of sequence `p` (counted from `0`): `θ (p / 2)`. -/
def θseq (p : ℕ) : ℚ := P.θ (p / 2)

/-- The time after the raise: `θ⁺ = (1 + ε²) θ`. -/
def θplus (θ : ℚ) : ℚ := (1 + P.ε ^ 2) * θ

/-- The conditions on the parameters (`n` is the number of clients). -/
structure Good (n : ℕ) : Prop where
  δ_pos : 0 < P.δ
  δ_le : P.δ ≤ 1 / 100
  ε_pos : 0 < P.ε
  ε_le : P.ε ≤ P.δ / 10
  η_nonneg : 0 ≤ P.η
  nη_le : n * P.η ≤ P.δ * P.ε / 10
  K_ge : 2 * P.θ P.R ≤ P.K

end Par

/-- Sequence `p` (counted from `0`) is of **type 1** if `p` is even. -/
def typ1 (p : ℕ) : Bool := p % 2 == 0

theorem Par.θ_succ (P : Par) (r : ℕ) : P.θ (r + 1) = (1 + P.ε ^ 2) * P.θ r := by
  unfold Par.θ
  ring

theorem Par.one_le_θ (P : Par) (r : ℕ) : 1 ≤ P.θ r :=
  one_le_pow₀ (by nlinarith [sq_nonneg P.ε])

theorem Par.θ_mono (P : Par) {r r' : ℕ} (h : r ≤ r') : P.θ r ≤ P.θ r' :=
  pow_le_pow_right₀ (by nlinarith [sq_nonneg P.ε]) h

theorem Par.θseq_mono (P : Par) {p p' : ℕ} (h : p ≤ p') : P.θseq p ≤ P.θseq p' :=
  P.θ_mono (Nat.div_le_div_right h)

/-! ### The inequalities between the parameters -/

namespace Par.Good

variable {P : Par} {n : ℕ} (h : P.Good n)
include h

theorem δ_le_sixth : P.δ ≤ 1 / 6 := by linarith [h.δ_le]

theorem one_sub_δ_pos : 0 < 1 - P.δ := by linarith [h.δ_le]

theorem half_le_one_sub_δ : 1 / 2 ≤ 1 - P.δ := by linarith [h.δ_le]

theorem ε_le_δ : P.ε ≤ P.δ := by linarith [h.ε_le, h.δ_pos]

theorem ε_le_one : P.ε ≤ 1 := by linarith [h.ε_le, h.δ_le]

/-- `2 ε ≤ δ`. -/
theorem two_ε_le : 2 * P.ε ≤ P.δ := by linarith [h.ε_le, h.δ_pos]

/-- `ε ≤ γ δ / 2` [key lemma, overbidding, pay-to-open]. -/
theorem ε_le_γδ : P.ε ≤ γ * P.δ / 2 := by
  have := h.ε_le; have := h.δ_pos; norm_num [γ]; linarith

/-- `γ ε < δ / 2` [structure lemma]. -/
theorem γε_lt : γ * P.ε < P.δ / 2 := by
  have := h.ε_le; have := h.ε_pos; norm_num [γ]; linarith

/-- `γ ε < 1` [the exact test]. -/
theorem γε_lt_one : γ * P.ε < 1 := by
  have := h.γε_lt; have := h.δ_le; linarith

/-- `ε ≤ δ / (1 - δ)` [superset-far]. -/
theorem ε_le_δ_div : P.ε ≤ P.δ / (1 - P.δ) := by
  rw [le_div_iff₀ h.one_sub_δ_pos]
  have := h.ε_le; have := h.δ_pos; have := h.δ_le
  nlinarith

/-- `n η ≤ γ δ / 2` [structure lemma]. -/
theorem nη_le_γδ : n * P.η ≤ γ * P.δ / 2 := by
  have := h.nη_le; have := h.ε_le; have := h.δ_pos; have := h.δ_le; have := h.ε_pos
  norm_num [γ]; nlinarith

/-- `n η < δ` [the smallest opening cost is above `n η`]. -/
theorem nη_lt_δ : n * P.η < P.δ := by
  have := h.nη_le; have := h.ε_le; have := h.δ_pos; have := h.δ_le; have := h.ε_pos
  nlinarith

/-- `2 ε² + n η ≤ γ δ (δ - ε) / 2` [structure lemma]. -/
theorem structure_ineq₁ : 2 * P.ε ^ 2 + n * P.η ≤ γ * P.δ * (P.δ - P.ε) / 2 := by
  have := h.nη_le; have := h.ε_le; have := h.δ_pos; have := h.δ_le; have := h.ε_pos
  norm_num [γ]; nlinarith

/-- `n η ≤ γ δ ε / 2 - ε²` [structure lemma]. -/
theorem structure_ineq₂ : n * P.η ≤ γ * P.δ * P.ε / 2 - P.ε ^ 2 := by
  have := h.nη_le; have := h.ε_le; have := h.δ_pos; have := h.δ_le; have := h.ε_pos
  norm_num [γ]; nlinarith

/-- `ε² (1 - δ) ≤ δ / 2` [structure lemma]. -/
theorem structure_ineq₃ : P.ε ^ 2 * (1 - P.δ) ≤ P.δ / 2 := by
  have := h.ε_le; have := h.δ_pos; have := h.δ_le; have := h.ε_pos
  nlinarith

/-- `(1 + ε²) / ρ < 1 / γ - ε` [freezing]. -/
theorem freezing_ineq : (1 + P.ε ^ 2) / ρ < 1 / γ - P.ε := by
  have := h.ε_le; have := h.δ_pos; have := h.δ_le; have := h.ε_pos
  rw [ρ_eq, γ]
  rw [div_lt_iff₀ (by norm_num)]
  nlinarith

/-- `1 - δ < ρ (1 - δ + δ²)` [freezing]. -/
theorem freezing_ineq₂ : 1 - P.δ < ρ * (1 - P.δ + P.δ ^ 2) := by
  have := h.δ_pos; have := h.δ_le
  rw [ρ_eq]
  nlinarith

end Par.Good

/-! ### Atoms -/

/-- An **atom**: an opened facility `fac`, regular or a free copy (`free`) at offset `off` from
its original. -/
structure Atom (m : ℕ) where
  /-- The facility, or the original of a free copy. -/
  fac : Fin m
  /-- The offset: `0` for a regular facility, the paper's `u(ĩ)` for a free copy. -/
  off : ℚ
  /-- Whether the atom is a free copy. -/
  free : Bool
deriving DecidableEq

/-- The pair `(fac, off)` of an atom: all the analysis sees of it. -/
def Atom.pair {m : ℕ} (a : Atom m) : Fin m × ℚ := (a.fac, a.off)

/-- A **well-formed** atom: regular atoms have offset `0`, offsets lie in `[0, K]`. -/
def Atom.WF {m : ℕ} (K : ℚ) (a : Atom m) : Prop :=
  (a.free = false → a.off = 0) ∧ 0 ≤ a.off ∧ a.off ≤ K

/-! ### Profiles -/

section Profiles

variable {n m : ℕ}

/-- The **profile** of a set `S` of pairs: client `j` is at distance
`min (K, min_{(i, u) ∈ S} d j i + u)` from it. -/
def profF (K : ℚ) (d : Fin n → Fin m → ℚ) (S : Finset (Fin m × ℚ)) (j : Fin n) : ℚ :=
  S.fold min K fun p ↦ d j p.1 + p.2

/-- The pairs of a list of atoms. -/
def pairs (S : List (Atom m)) : Finset (Fin m × ℚ) := (S.map Atom.pair).toFinset

/-- The profile of a list of atoms: that of its set of pairs. -/
def profL (K : ℚ) (d : Fin n → Fin m → ℚ) (S : List (Atom m)) : Fin n → ℚ := profF K d (pairs S)

variable (K : ℚ) (d : Fin n → Fin m → ℚ)

theorem profF_empty (j : Fin n) : profF K d ∅ j = K := by simp [profF]

theorem profF_insert (S : Finset (Fin m × ℚ)) (p : Fin m × ℚ) (j : Fin n) :
    profF K d (insert p S) j = min (d j p.1 + p.2) (profF K d S j) := by
  classical
  exact Finset.fold_insert_idem

theorem profF_le_K (S : Finset (Fin m × ℚ)) (j : Fin n) : profF K d S j ≤ K :=
  (Finset.fold_min_le _).2 (.inl le_rfl)

theorem profF_le {S : Finset (Fin m × ℚ)} {p : Fin m × ℚ} (hp : p ∈ S) (j : Fin n) :
    profF K d S j ≤ d j p.1 + p.2 :=
  (Finset.fold_min_le _).2 (.inr ⟨p, hp, le_rfl⟩)

theorem le_profF {S : Finset (Fin m × ℚ)} {c : ℚ} {j : Fin n} (hK : c ≤ K)
    (hS : ∀ p ∈ S, c ≤ d j p.1 + p.2) : c ≤ profF K d S j :=
  (Finset.le_fold_min _).2 ⟨hK, hS⟩

/-- If the profile is below the cap, it is attained by a pair. -/
theorem exists_profF_eq {S : Finset (Fin m × ℚ)} {j : Fin n} (h : profF K d S j < K) :
    ∃ p ∈ S, profF K d S j = d j p.1 + p.2 := by
  rcases (Finset.fold_min_le (s := S) (b := K) (f := fun p ↦ d j p.1 + p.2)
    (profF K d S j)).1 le_rfl with hK | ⟨p, hp, hle⟩
  · exact absurd h (not_lt.2 hK)
  · exact ⟨p, hp, le_antisymm (profF_le K d hp j) hle⟩

/-- Profiles are antitone in the set. -/
theorem profF_anti {S S' : Finset (Fin m × ℚ)} (h : S ⊆ S') (j : Fin n) :
    profF K d S' j ≤ profF K d S j :=
  le_profF K d (profF_le_K K d S' j) fun _ hp ↦ profF_le K d (h hp) j

/-- A pair at offset at least `K` is invisible. -/
theorem profF_insert_of_le {S : Finset (Fin m × ℚ)} {p : Fin m × ℚ}
    (hd : ∀ j, 0 ≤ d j p.1) (hp : K ≤ p.2) : profF K d (insert p S) = profF K d S := by
  funext j
  rw [profF_insert]
  have := profF_le_K K d S j
  have := hd j
  exact min_eq_right (by linarith)

/-- Profiles are `1`-Lipschitz for client–client distances. -/
theorem profF_lipschitz {m : ℕ} (X : Space n m) (S : Finset (Fin m × ℚ)) (j k : Fin n) :
    profF K X.d S j ≤ profF K X.d S k + X.dC j k := by
  have hC : 0 ≤ X.dC j k := X.nonneg _ _
  rcases lt_or_ge (profF K X.d S k) K with h | h
  · obtain ⟨p, hp, heq⟩ := exists_profF_eq K X.d h
    have h1 := profF_le K X.d hp j
    have h2 := X.d_le_dC_add j k p.1
    linarith
  · have := profF_le_K K X.d S j
    linarith

theorem pairs_append (S T : List (Atom m)) : pairs (S ++ T) = pairs S ∪ pairs T := by
  simp [pairs, List.toFinset_append]

theorem profL_append (S T : List (Atom m)) :
    profL K d (S ++ T) = profF K d (pairs S ∪ pairs T) := by
  unfold profL
  rw [pairs_append]

theorem profL_congr {S T : List (Atom m)} (h : pairs S = pairs T) : profL K d S = profL K d T :=
  by unfold profL; rw [h]

/-- Profiles of lists are antitone in the set of pairs. -/
theorem profL_anti {S T : List (Atom m)} (h : pairs S ⊆ pairs T) (j : Fin n) :
    profL K d T j ≤ profL K d S j := profF_anti K d h j

end Profiles

end BCFGJPSSV26.Greedy


