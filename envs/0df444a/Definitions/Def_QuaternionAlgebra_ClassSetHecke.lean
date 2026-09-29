-- Prove2me | Definitions.Def_QuaternionAlgebra_ClassSetHecke
-- name    : QuaternionAlgebra_ClassSetHecke
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/3bb2e9bb-c330-520a-8e31-9440b10bf3c6
-- title:
--   Adelic class sets, Hecke kernels and congruence levels for quaternion algebras
-- statement:
--   Fix rationals $a,b$ and write $\widehat{\mathbb H} = \mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb A^f$, where $\mathbb A^f$ is the finite adele ring of $\mathbb Q$. For a subgroup $U\le\widehat{\mathbb H}^\times$, `ClassSet U` is the double-coset quotient of $\widehat{\mathbb H}^\times$ by the image of the diagonal map $\mathbb H^\times\to\widehat{\mathbb H}^\times$, $\delta\mapsto\delta\otimes 1$, on the left and by $U$ on the right; `ClassSet.mk` is the (surjective) class map, `ClassSet.map` the projection `ClassSet U → ClassSet U'` induced by $U\le U'$ (also surjective), and two lemmas record invariance of a class under right multiplication by $U$ and left multiplication by a diagonal element. For $S\subseteq\widehat{\mathbb H}^\times$, $x\in\widehat{\mathbb H}^\times$ and $y\in$ `ClassSet U`, `HeckeIncidence` is the subtype of the coset space $\widehat{\mathbb H}^\times/U$ consisting of those cosets $c$ admitting a representative $h\in S$ with class $c$ and $[xh]=y$; `heckeKernel U S x y` is the cardinality of this set, for a chosen representative of the class $x$, viewed in $\mathbb Z$. Under the hypothesis $US\subseteq S$ there is a bijection `HeckeIncidence U S (x*u) y ≃ HeckeIncidence U S x y` for $u\in U$, whence `heckeKernel_mk`: the kernel at $[x]$ equals the cardinality of the incidence set at $x$ itself, so the count is representative-independent.
--
--   Levels and Hecke sets are defined through the finite-adelic box $\widehat\Lambda$ of a $\mathbb Z$-lattice $\Lambda\subset\mathbb H$. For $\ell\in\mathbb N$, `primeHeckeSet` is the set of units $h$ with $h\in\widehat\Lambda$, $\ell h^{-1}\in\widehat\Lambda$, $h^{-1}\notin\widehat\Lambda$ and $\ell^{-1}h\notin\widehat\Lambda$; `levelHeckeSet` intersects this with $\{h: h-1\in\widehat P\}$ for a second lattice $P$. `congruenceLevel Λ P` is the subgroup of units stabilising the sets $\widehat\Lambda$ and $\widehat P$ and satisfying $ux-x\in\widehat P$ for all $x\in\widehat\Lambda$; it is contained in the stabiliser of $\widehat\Lambda$. Finally `normIdeal Λ q` is the $\mathbb Z$-span of the products $xyz$ with $x,y,z\in\Lambda$ and $\mathrm{nrd}(y)\in q\mathbb Z$, with $\mathrm{nrd}$ the reduced norm; when $\Lambda$ satisfies `IsOrder` (unital, multiplicatively closed, $\mathbb Q$-spanning, finitely generated) this span is a two-sided $\Lambda$-submodule of $\Lambda$ containing $q\Lambda$.
--
--   **Relation to Mathlib.** Mathlib supplies the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, the finite adele ring and the double-coset quotient; the adelic class set, the Hecke incidence sets and kernels, the prime and level Hecke sets, the congruence level subgroups and the norm ideal are the project's own notions, built on the project's finite-adelic box and reduced norm.
--
--   **Where it is used.** These are the carriers of the Brandt–Eichler Hecke module of a definite quaternion algebra in adelic form: functions on a class set $\mathbb H^\times\backslash\widehat{\mathbb H}^\times/U$ with Hecke operators given by the incidence counts, used in the Jacquet–Langlands comparison with weight-two modular forms and in the argument at a ramified prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_QuaternionAlgebra_ClassSetHecke.lean

import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Pointwise Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace QuaternionAlgebra

variable {a b : ℚ}

abbrev ClassSet (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Type :=
  DoubleCoset.Quotient
    (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range :
        Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (U : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)

namespace ClassSet

variable {U U' : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}

variable (U) in

abbrev mk (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ClassSet U :=
  DoubleCoset.mk (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range U x

theorem mk_surjective : Function.Surjective (mk U) := Quotient.mk''_surjective

def map (h : U ≤ U') : ClassSet U → ClassSet U' :=
  Quotient.map' id fun x y hxy => by
    obtain ⟨c, hc, d, hd, rfl⟩ := DoubleCoset.rel_iff.mp hxy
    exact DoubleCoset.rel_iff.mpr ⟨c, hc, d, h hd, rfl⟩

@[simp] theorem map_mk (h : U ≤ U') (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    map h (mk U x) = mk U' x := rfl

theorem map_surjective (h : U ≤ U') : Function.Surjective (map h) := by
  rintro ⟨x⟩; exact ⟨mk U x, rfl⟩

theorem mk_mul_of_mem (x u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hu : u ∈ U) :
    mk U (x * u) = mk U x :=
  ((DoubleCoset.eq _ _ _ _).mpr ⟨1, one_mem _, u, hu, by rw [one_mul]⟩).symm

theorem mk_diagonal_mul (δ : (ℍ[ℚ, a, b])ˣ) (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    mk U (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x) = mk U x :=
  ((DoubleCoset.eq _ _ _ _).mpr
    ⟨Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ, MonoidHom.mem_range.mpr ⟨δ, rfl⟩, 1, one_mem _,
      by rw [mul_one]⟩).symm

end ClassSet

section HeckeKernel

def HeckeIncidence (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (y : ClassSet U) : Type :=
  {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U //
    ∃ h ∈ S, (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) = c ∧ ClassSet.mk U (x * h) = y}

def heckeKernel (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (x y : ClassSet U) : ℤ :=
  Nat.card (HeckeIncidence U S x.out y)

def heckeIncidenceEquiv (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hS : ∀ u ∈ U, ∀ s ∈ S, u * s ∈ S)
    (x u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hu : u ∈ U) (y : ClassSet U) :
    HeckeIncidence U S (x * u) y ≃ HeckeIncidence U S x y where
  toFun c := ⟨u • c.1, by
    obtain ⟨h, hh, hc, hy⟩ := c.2
    refine ⟨u * h, hS u hu h hh, ?_, ?_⟩
    · rw [← hc]; rfl
    · rwa [← mul_assoc]⟩
  invFun c := ⟨u⁻¹ • c.1, by
    obtain ⟨h, hh, hc, hy⟩ := c.2
    refine ⟨u⁻¹ * h, hS u⁻¹ (inv_mem hu) h hh, ?_, ?_⟩
    · rw [← hc]; rfl
    · rwa [← mul_assoc, mul_inv_cancel_right]⟩
  left_inv c := Subtype.ext (by simp)
  right_inv c := Subtype.ext (by simp)

theorem heckeKernel_mk (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hS : ∀ u ∈ U, ∀ s ∈ S, u * s ∈ S)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (y : ClassSet U) :
    heckeKernel U S (ClassSet.mk U x) y = Nat.card (HeckeIncidence U S x y) := by
  obtain ⟨δ, u, hδ, hu, hout⟩ :=
    DoubleCoset.mk_out_eq_mul (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range U x
  unfold heckeKernel
  rw [show (ClassSet.mk U x).out = δ * x * u from hout]
  have e1 : HeckeIncidence U S (δ * x * u) y ≃ HeckeIncidence U S (δ * x) y :=
    heckeIncidenceEquiv U S hS (δ * x) u hu y
  have e2 : HeckeIncidence U S (δ * x) y ≃ HeckeIncidence U S x y := by
    refine Equiv.subtypeEquivRight fun c => ?_
    obtain ⟨δ', rfl⟩ := MonoidHom.mem_range.mp hδ
    simp only [mul_assoc, ClassSet.mk_diagonal_mul]
  rw [Nat.card_congr (e1.trans e2)]

end HeckeKernel

section Level

def primeHeckeSet (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) :
    Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  {h | (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ∧
    (ℓ : ℚ) • ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ∧
    ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
        ∉ Submodule.finiteAdeleBox Λ ∧
    (ℓ : ℚ)⁻¹ • (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∉ Submodule.finiteAdeleBox Λ}

theorem mem_primeHeckeSet_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ)
    (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    h ∈ primeHeckeSet Λ ℓ ↔
      (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ∧
      (ℓ : ℚ) • ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ∧
      ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
          ∉ Submodule.finiteAdeleBox Λ ∧
      (ℓ : ℚ)⁻¹ • (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∉ Submodule.finiteAdeleBox Λ :=
  Iff.rfl

def levelHeckeSet (Λ P : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) :
    Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  primeHeckeSet Λ ℓ ∩
    {h | (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) - 1 ∈ Submodule.finiteAdeleBox P}

theorem mem_levelHeckeSet_iff (Λ P : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ)
    (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    h ∈ levelHeckeSet Λ P ℓ ↔
      h ∈ primeHeckeSet Λ ℓ ∧
        (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) - 1 ∈ Submodule.finiteAdeleBox P :=
  Iff.rfl

def congruenceLevel (Λ P : Submodule ℤ ℍ[ℚ, a, b]) :
    Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ where
  carrier := {u | u ∈ Submodule.finiteIdeleStabilizer Λ ∧ u ∈ Submodule.finiteIdeleStabilizer P ∧
    ∀ x ∈ Submodule.finiteAdeleBox Λ,
      (u : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * x - x ∈ Submodule.finiteAdeleBox P}
  one_mem' := ⟨one_mem _, one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro u v ⟨huΛ, huP, hu⟩ ⟨hvΛ, hvP, hv⟩
    refine ⟨mul_mem huΛ hvΛ, mul_mem huP hvP, fun x hx => ?_⟩
    have h1 : (u : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * ((v : _) * x - x) ∈
        Submodule.finiteAdeleBox P := by
      have hmem : (u : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * ((v : _) * x - x) ∈
          u • ((Submodule.finiteAdeleBox P : AddSubgroup _) :
            Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
        Set.smul_mem_smul_set (hv x hx)
      rwa [(Submodule.mem_finiteIdeleStabilizer_iff P u).mp huP] at hmem
    have h2 := hu x hx
    have : ((u * v : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * x - x
        = (u : _) * ((v : _) * x - x) + ((u : _) * x - x) := by
      rw [Units.val_mul, mul_sub, mul_assoc]; abel
    rw [this]
    exact add_mem h1 h2
  inv_mem' := by
    rintro u ⟨huΛ, huP, hu⟩
    refine ⟨inv_mem huΛ, inv_mem huP, fun x hx => ?_⟩
    have hy : ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : _) * x ∈
        Submodule.finiteAdeleBox Λ := by
      have hmem : ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : _) * x ∈
          u⁻¹ • ((Submodule.finiteAdeleBox Λ : AddSubgroup _) :
            Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
        Set.smul_mem_smul_set hx
      rwa [(Submodule.mem_finiteIdeleStabilizer_iff Λ u⁻¹).mp (inv_mem huΛ)] at hmem
    have h := hu _ hy
    rw [← mul_assoc, Units.mul_inv, one_mul] at h
    rw [← neg_sub]
    exact neg_mem h

theorem mem_congruenceLevel_iff (Λ P : Submodule ℤ ℍ[ℚ, a, b])
    (u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    u ∈ congruenceLevel Λ P ↔
      u ∈ Submodule.finiteIdeleStabilizer Λ ∧ u ∈ Submodule.finiteIdeleStabilizer P ∧
        ∀ x ∈ Submodule.finiteAdeleBox Λ,
          (u : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * x - x ∈ Submodule.finiteAdeleBox P :=
  Iff.rfl

theorem congruenceLevel_le (Λ P : Submodule ℤ ℍ[ℚ, a, b]) :
    congruenceLevel Λ P ≤ Submodule.finiteIdeleStabilizer Λ := fun _ hu => hu.1

def normIdeal (Λ : Submodule ℤ ℍ[ℚ, a, b]) (q : ℕ) : Submodule ℤ ℍ[ℚ, a, b] :=
  Submodule.span ℤ {w | ∃ x ∈ Λ, ∃ y ∈ Λ, ∃ z ∈ Λ, (∃ m : ℤ, nrd y = (q : ℚ) * m) ∧ w = x * y * z}

theorem mul_mul_mem_normIdeal {Λ : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} {x y z : ℍ[ℚ, a, b]}
    (hx : x ∈ Λ) (hy : y ∈ Λ) (hz : z ∈ Λ) (m : ℤ) (hm : nrd y = (q : ℚ) * m) :
    x * y * z ∈ normIdeal Λ q :=
  Submodule.subset_span ⟨x, hx, y, hy, z, hz, ⟨m, hm⟩, rfl⟩

theorem IsOrder.normIdeal_le {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (q : ℕ) :
    normIdeal Λ q ≤ Λ := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, hx, y, hy, z, hz, -, rfl⟩
  exact hΛ.mul_mem (hΛ.mul_mem hx hy) hz

theorem IsOrder.mul_mem_normIdeal {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {q : ℕ}
    {x w : ℍ[ℚ, a, b]} (hx : x ∈ Λ) (hw : w ∈ normIdeal Λ q) : x * w ∈ normIdeal Λ q := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x', hx', y, hy, z, hz, ⟨m, hm⟩, rfl⟩ := hw
    simpa only [mul_assoc] using mul_mul_mem_normIdeal (hΛ.mul_mem hx hx') hy hz m hm
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
  | smul n u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ n hu

theorem IsOrder.mul_mem_normIdeal_right {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {q : ℕ}
    {w z : ℍ[ℚ, a, b]} (hw : w ∈ normIdeal Λ q) (hz : z ∈ Λ) : w * z ∈ normIdeal Λ q := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, y, hy, z', hz', ⟨m, hm⟩, rfl⟩ := hw
    simpa only [mul_assoc] using mul_mul_mem_normIdeal hx hy (hΛ.mul_mem hz' hz) m hm
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | smul n u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ n hu

theorem IsOrder.natCast_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (n : ℕ) :
    (n : ℍ[ℚ, a, b]) ∈ Λ := by
  simpa using Submodule.smul_mem Λ (n : ℤ) hΛ.one_mem

theorem IsOrder.natCast_mul_mem_normIdeal {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (q : ℕ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : (q : ℍ[ℚ, a, b]) * x ∈ normIdeal Λ q := by
  have h := mul_mul_mem_normIdeal (q := q) hΛ.one_mem (hΛ.natCast_mem q) hx (q : ℤ) (by
    rw [show (q : ℍ[ℚ, a, b]) = ((q : ℚ) : ℍ[ℚ, a, b]) by norm_cast, nrd_coe]; push_cast; ring)
  simpa using h

theorem IsOrder.natCast_smul_mem_normIdeal {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (q : ℕ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : ((q : ℕ) : ℤ) • x ∈ normIdeal Λ q := by
  have h := hΛ.natCast_mul_mem_normIdeal q hx
  rwa [show (q : ℍ[ℚ, a, b]) * x = ((q : ℕ) : ℤ) • x by
    rw [zsmul_eq_mul, Int.cast_natCast]] at h

end Level

end QuaternionAlgebra

end


