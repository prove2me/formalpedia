-- Prove2me | Definitions.Def_WeatherallGauge_defs
-- name    : WeatherallGauge_defs
-- status  : Definition
-- author  : @Alien60
-- created : 2026-10-09T21:16:18.528792+00:00
-- url     : https://prove2.me/theorems/a422d226-1e45-487d-992b-c6b85579710b
-- title:
--   Cochains on a finite 2-complex and the categories of potentials and field strengths
-- statement:
--   A finite oriented 2-complex `CellComplex2` ($n_V,n_E,n_P$ cells indexed by `Fin`, integer incidences `bd1`, `bd2` with $\sum_e \partial_2(p,e)\partial_1(e,v)=0$); $K$-valued cochains `C0`, `C1`, `C2`; coboundaries `delta0`, `delta1` with $\delta^1\delta^0=0$ (proved); elementary vanishing conditions `H0Vanishes`, `H1Vanishes`, `H2Vanishes`; the discrete categories `Fld` (EM1) and `Pot0` (EM2, trivial symmetries); the category `PotG` of potentials with gauge arrows $\lambda: A\to A'$ iff $A+\delta^0\lambda=A'$; the functors `fieldStrength0`, `fieldStrength` sending $A\mapsto\delta^1A$; and the examples `circle3` and `filledTriangle`.
-- source:
--   J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016) 1039-1049, https://arxiv.org/abs/1505.02229 (page numbers refer to arXiv v2), §4 pp. 7–11 (EM1, EM2, EM3, Props. 1–2, fn. 9, fn. 15; erratum to Prop. 2, p. 15)

import Mathlib

/-!
# Weatherall's "potentials vs. field strengths" on a finite 2-complex

Discrete setting for J. O. Weatherall, "Understanding Gauge", Philos. Sci. 83 (2016),
§4 (arXiv:1505.02229). Minkowski space is replaced by a finite oriented 2-complex `X`,
differential forms by `K`-valued cochains, and the exterior derivative by the coboundary.
Spacetime symmetries are taken to be trivial (only identities).

* `Pot0 X K`  — Weatherall's EM2: potentials, only identity arrows.
* `PotG X K`  — EM2 with gauge transformations `A ↦ A + δλ` as arrows (fn. 15 / EM3).
* `Fld X K`   — Weatherall's EM1: field strengths, only identity arrows.
* `fieldStrength0 : Pot0 ⥤ Fld`, `fieldStrength : PotG ⥤ Fld` — the functor `A ↦ δA`.
-/

open CategoryTheory

namespace WeatherallGauge

/-- A finite oriented 2-dimensional cell complex with `nV` vertices, `nE` edges and `nP`
faces. `bd1 e v` is the incidence number of vertex `v` in the boundary of edge `e`,
`bd2 p e` that of edge `e` in the boundary of face `p`; boundaries of boundaries vanish. -/
structure CellComplex2 where
  nV : ℕ
  nE : ℕ
  nP : ℕ
  bd1 : Fin nE → Fin nV → ℤ
  bd2 : Fin nP → Fin nE → ℤ
  bd_bd : ∀ p v, ∑ e, bd2 p e * bd1 e v = 0

variable (X : CellComplex2) (K : Type) [AddCommGroup K]

/-- `K`-valued 0-cochains (gauge parameters / scalar fields). -/
abbrev C0 := Fin X.nV → K
/-- `K`-valued 1-cochains (potentials). -/
abbrev C1 := Fin X.nE → K
/-- `K`-valued 2-cochains (field strengths). -/
abbrev C2 := Fin X.nP → K

variable {X K}

/-- Coboundary on 0-cochains: `(δ⁰λ)(e) = ∑_v [e : v] λ(v)`. -/
def delta0 (lam : C0 X K) : C1 X K := fun e => ∑ v, X.bd1 e v • lam v

/-- Coboundary on 1-cochains: `(δ¹A)(p) = ∑_e [p : e] A(e)`. -/
def delta1 (A : C1 X K) : C2 X K := fun p => ∑ e, X.bd2 p e • A e

theorem delta0_add (a b : C0 X K) : delta0 (a + b) = delta0 a + delta0 b := by
  funext e; simp [delta0, smul_add, Finset.sum_add_distrib]

theorem delta0_zero : delta0 (0 : C0 X K) = 0 := by
  funext e; simp [delta0]

theorem delta1_add (a b : C1 X K) : delta1 (a + b) = delta1 a + delta1 b := by
  funext p; simp [delta1, smul_add, Finset.sum_add_distrib]

theorem delta1_delta0 (lam : C0 X K) : delta1 (delta0 lam) = 0 := by
  funext p
  simp only [delta1, delta0, Finset.smul_sum, smul_smul, Pi.zero_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, X.bd_bd, zero_smul, Finset.sum_const_zero]

/-! ### Elementary cohomology-vanishing conditions -/

/-- `H⁰(X;K) = 0`: the only 0-cochain with vanishing coboundary is zero. -/
def H0Vanishes (X : CellComplex2) (K : Type) [AddCommGroup K] : Prop :=
  ∀ lam : C0 X K, delta0 lam = 0 → lam = 0

/-- `H¹(X;K) = 0`: every closed 1-cochain is exact. -/
def H1Vanishes (X : CellComplex2) (K : Type) [AddCommGroup K] : Prop :=
  ∀ A : C1 X K, delta1 A = 0 → ∃ lam : C0 X K, delta0 lam = A

/-- `H²(X;K) = 0`: every 2-cochain is exact (there are no 3-cells). -/
def H2Vanishes (X : CellComplex2) (K : Type) [AddCommGroup K] : Prop :=
  ∀ F : C2 X K, ∃ A : C1 X K, delta1 A = F

/-! ### The categories -/

/-- Weatherall's EM1: field strengths, with only identity arrows. -/
abbrev Fld (X : CellComplex2) (K : Type) [AddCommGroup K] := Discrete (C2 X K)

/-- Weatherall's EM2 (trivial symmetries): potentials, with only identity arrows. -/
abbrev Pot0 (X : CellComplex2) (K : Type) [AddCommGroup K] := Discrete (C1 X K)

/-- Potentials with gauge arrows: an arrow `A ⟶ A'` is a gauge parameter `λ` with
`A + δ⁰λ = A'`. -/
structure PotG (X : CellComplex2) (K : Type) [AddCommGroup K] where
  /-- The underlying potential. -/
  pot : C1 X K

/-- Gauge transformations from `A` to `A'`. -/
@[ext]
structure GaugeHom (A A' : PotG X K) where
  /-- The gauge parameter. -/
  lam : C0 X K
  eq : A.pot + delta0 lam = A'.pot

instance : Category (PotG X K) where
  Hom := GaugeHom
  id A := ⟨0, by simp [delta0_zero]⟩
  comp f g := ⟨f.lam + g.lam, by rw [delta0_add, ← add_assoc, f.eq, g.eq]⟩
  id_comp f := GaugeHom.ext (zero_add _)
  comp_id f := GaugeHom.ext (add_zero _)
  assoc f g h := GaugeHom.ext (add_assoc _ _ _)

/-- The field-strength functor on `Pot0`: `A ↦ δ¹A`. -/
def fieldStrength0 : Pot0 X K ⥤ Fld X K :=
  Discrete.functor fun A => Discrete.mk (delta1 A)

/-- The field-strength functor on `PotG`: `A ↦ δ¹A`; a gauge arrow goes to the identity,
since `δ¹(A + δ⁰λ) = δ¹A`. -/
def fieldStrength : PotG X K ⥤ Fld X K where
  obj A := Discrete.mk (delta1 A.pot)
  map {A A'} f := eqToHom (by rw [← f.eq, delta1_add, delta1_delta0, add_zero])

end WeatherallGauge

namespace WeatherallGauge

/-! ### Example complexes -/

/-- The boundary of a triangle (a circle): vertices `0,1,2`, edge `e` runs from `e` to
`e+1 mod 3`, no faces. Here `H¹ ≠ 0` (Aharonov–Bohm setting). -/
abbrev circle3 : CellComplex2 where
  nV := 3
  nE := 3
  nP := 0
  bd1 e v := if v = e + 1 then 1 else if v = e then -1 else 0
  bd2 p _ := p.elim0
  bd_bd p _ := p.elim0

/-- The filled triangle: `circle3` with one face whose boundary is the sum of the three
edges. Here `H¹ = H² = 0` but `H⁰ ≠ 0`. -/
abbrev filledTriangle : CellComplex2 where
  nV := 3
  nE := 3
  nP := 1
  bd1 e v := if v = e + 1 then 1 else if v = e then -1 else 0
  bd2 _ _ := 1
  bd_bd _ v := by fin_cases v <;> decide

end WeatherallGauge


