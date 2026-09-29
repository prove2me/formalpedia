-- Prove2me | Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
-- name    : AlgebraicGeometry_BoundedCochainTensor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/5fc598d9-50a8-5476-91a5-26fdabcfb3ca
-- title:
--   Bounded cochain complexes, cohomology, tensor double complex
-- statement:
--   Over a commutative ring $R$, [`CochainCx.Bounded R`](../def/AlgebraicGeometry_BoundedCochainTensor.html#L26) is a structure packaging an $\mathbb N$-indexed cochain complex of $R$-modules: a family of $R$-modules $X^n$, $R$-linear maps $d^n \colon X^n \to X^{n+1}$, the condition $d^{n+1} \circ d^n = 0$ for all $n$ as a field, and a natural number $N$ together with a proof that $X^n$ is a subsingleton (so the zero module) for every $n \ge N$. Cohomology is spelled uniformly as a quotient inside the kernel: `B` is defined by $B^0 = \bot$ and $B^{n+1} =$ the preimage of $\operatorname{im} d^n$ under the inclusion $\ker d^{n+1} \hookrightarrow X^{n+1}$, and `H n` is $\ker d^n / B^n$; `hfinrank n` is its $R$-rank, $\operatorname{finrank}_R H^n$. Two equations record $B^0 = \bot$ and the formula for $B^{n+1}$.
--
--   Given two such complexes $C$, $D$, `tensor` is the bounded double complex (in the sense of [`DoubleComplex.Bounded R`](../def/AlgebraicGeometry_DoubleComplex.html#L11)) with $(p,q)$-term $C^p \otimes_R D^q$, horizontal differential $d_C^p \otimes \mathrm{id}$ and vertical differential $\mathrm{id} \otimes d_D^q$; the squares commute on the nose (the Koszul sign enters only through the total differential of the double-complex structure), and the bound is $\max(C.N, D.N)$, the two vanishing conditions being inherited from the factors. Accompanying equations identify its terms, its two differentials and its bound.
--
--   `ofCech` turns Čech data into such a complex: for a presheaf of modules $F$ on a scheme $V$ over $\operatorname{Spec} R$ (an `OModulePresheaf` for $\pi \colon V \to \operatorname{Spec} R$), a finite ordered affine cover $K$ of $V$, and a hypothesis that the alternating Čech differentials satisfy $d^{i+1} \circ d^i = 0$, the complex has $X^i = \prod_{s} F(\bigcap_j U_{s(j)})$ over the strictly increasing $(i+1)$-tuples $s$, differentials those of $F$, and bound $\#K.\iota$, since there are no strictly increasing tuples of length exceeding the number of indices. Further equations identify its terms and differentials with the Čech ones, its $H^{i+1}$ with `OModulePresheaf.HSucc`, and its $H^0$ with the quotient of `OModulePresheaf.H0` by the zero submodule. Finally, `preimageFamily` sends a finite ordered affine cover $K$ of $Y$ and a morphism $q \colon P \to Y$ to the ordered open family on $P$ with the same index type and opens $q^{-1}(U_i)$, with equations for its index type and its opens.
--
--   **Relation to Mathlib.** Mathlib's homological algebra works with `HomologicalComplex` and its homology; the complexes here are the project's own lightweight $\mathbb N$-graded bounded complexes of $R$-modules, with cohomology presented concretely as $\ker d^n$ modulo an explicitly defined submodule of coboundaries, and similarly for the double complexes they feed.
--
--   **Where it is used.** These bounded complexes provide the algebraic frame for the alternating Čech complex of a finite ordered affine cover, and the tensor double complex together with the preimage families of a product are what a Künneth-style comparison of Čech cohomology on products is formulated against.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_BoundedCochainTensor.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open TensorProduct AlgebraicGeometry

@[reducible] def AlgebraicGeometry.Scheme.OrderedAffineCover.preimageFamily {P Y : Scheme.{u}} (K : Y.OrderedAffineCover)
    (q : P ⟶ Y) : P.OrderedOpenFamily :=
  ⟨K.ι, fun i => q ⁻¹ᵁ K.U i⟩

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.preimageFamily_ι {P Y : Scheme.{u}} (K : Y.OrderedAffineCover)
    (q : P ⟶ Y) : (K.preimageFamily q).ι = K.ι := rfl

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.preimageFamily_U {P Y : Scheme.{u}} (K : Y.OrderedAffineCover)
    (q : P ⟶ Y) (i : K.ι) : (K.preimageFamily q).U i = q ⁻¹ᵁ K.U i := rfl

namespace CochainCx

structure Bounded (R : Type u) [CommRing R] where

  X : ℕ → Type u
  [abGrp : ∀ n, AddCommGroup (X n)]
  [modR : ∀ n, Module R (X n)]

  d : ∀ n, X n →ₗ[R] X (n + 1)
  d_sq : ∀ n, d (n + 1) ∘ₗ d n = 0

  N : ℕ
  hBound : ∀ n, N ≤ n → Subsingleton (X n)

attribute [instance] Bounded.abGrp Bounded.modR

namespace Bounded

variable {R : Type u} [CommRing R] (C D : Bounded R)

def B : (n : ℕ) → Submodule R (LinearMap.ker (C.d n))
  | 0 => ⊥
  | n + 1 => (LinearMap.range (C.d n)).comap (LinearMap.ker (C.d (n + 1))).subtype

abbrev H (n : ℕ) : Type u := LinearMap.ker (C.d n) ⧸ C.B n

abbrev hfinrank (n : ℕ) : ℕ := Module.finrank R (C.H n)

theorem B_zero : C.B 0 = ⊥ := rfl

theorem B_succ (n : ℕ) :
    C.B (n + 1) = (LinearMap.range (C.d n)).comap (LinearMap.ker (C.d (n + 1))).subtype := rfl

def tensor : DoubleComplex.Bounded R where
  C p q := C.X p ⊗[R] D.X q
  dH p q := (C.d p).rTensor (D.X q)
  dV p q := (D.d q).lTensor (C.X p)
  dH_sq p q := by
    rw [← LinearMap.rTensor_comp, C.d_sq, LinearMap.rTensor_zero]
  dV_sq p q := by
    rw [← LinearMap.lTensor_comp, D.d_sq, LinearMap.lTensor_zero]
  dHV_comm p q := by
    ext x y
    simp [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  N := max C.N D.N
  hBound p q h := by
    rcases h with h | h
    · haveI := C.hBound p (le_of_max_le_left h)
      infer_instance
    · haveI := D.hBound q (le_of_max_le_right h)
      infer_instance

theorem tensor_C (p q : ℕ) : (C.tensor D).C p q = (C.X p ⊗[R] D.X q) := rfl
theorem tensor_dH (p q : ℕ) : (C.tensor D).dH p q = (C.d p).rTensor (D.X q) := rfl
theorem tensor_dV (p q : ℕ) : (C.tensor D).dV p q = (D.d q).lTensor (C.X p) := rfl
theorem tensor_N : (C.tensor D).N = max C.N D.N := rfl

def ofCech {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (F : OModulePresheaf π) (K : V.OrderedAffineCover)
    (hdd : ∀ i, F.d K (i + 1) ∘ₗ F.d K i = 0) : Bounded R where
  X i := F.cochain K i
  d i := F.d K i
  d_sq := hdd
  N := Fintype.card K.ι
  hBound n hn := by
    haveI : IsEmpty (K.Idx n) := by
      refine ⟨fun s => ?_⟩
      have := Fintype.card_le_of_injective s.1 s.2.injective
      simp only [Fintype.card_fin] at this
      omega
    infer_instance

theorem ofCech_X {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (F : OModulePresheaf π) (K : V.OrderedAffineCover)
    (hdd : ∀ i, F.d K (i + 1) ∘ₗ F.d K i = 0) (i : ℕ) : (ofCech F K hdd).X i = F.cochain K i := rfl

theorem ofCech_d {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (F : OModulePresheaf π) (K : V.OrderedAffineCover)
    (hdd : ∀ i, F.d K (i + 1) ∘ₗ F.d K i = 0) (i : ℕ) : (ofCech F K hdd).d i = F.d K i := rfl

theorem ofCech_H_succ {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (F : OModulePresheaf π) (K : V.OrderedAffineCover)
    (hdd : ∀ i, F.d K (i + 1) ∘ₗ F.d K i = 0) (i : ℕ) : (ofCech F K hdd).H (i + 1) = F.HSucc K i := rfl

theorem ofCech_H_zero {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (F : OModulePresheaf π) (K : V.OrderedAffineCover)
    (hdd : ∀ i, F.d K (i + 1) ∘ₗ F.d K i = 0) :
    (ofCech F K hdd).H 0 = ((F.H0 K) ⧸ (⊥ : Submodule R (F.H0 K))) := rfl

end Bounded

end CochainCx

end


