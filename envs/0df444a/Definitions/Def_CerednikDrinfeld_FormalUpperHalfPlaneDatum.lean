-- Prove2me | Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
-- name    : CerednikDrinfeld_FormalUpperHalfPlaneDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/6f416f5a-8fea-5e26-a73a-5f0c35210d8e
-- title:
--   Deligne lattice data for the formal upper half plane
-- statement:
--   Fix a commutative ring $\mathcal{O}$, a field $K$ with an $\mathcal{O}$-algebra structure, and an element $\pi \in \mathcal{O}$; lattices are indexed by the type `FullLattice 𝒪 K` of full $\mathcal{O}$-lattices $M$ in $K^{2}$. For a commutative $\mathcal{O}$-algebra $B$ write $B \otimes_{\mathcal{O}} M$ for `latticeBaseChange`. The helpers provide the base change `inclBaseChange` of an inclusion $M' \le M$, the $\mathcal{O}$-linear isomorphism `latticeMapEquiv` from $M$ onto its image `latticeMap g M` under $v \mapsto g\cdot v$ for $g \in \mathrm{GL}_2(K)$ (with `mulVecLinR_injective` as the required injectivity, proved by multiplying by $g^{-1}$), the induced action `FullLattice.act` on full lattices, and its $B$-linear base change `actBaseChange`.
--
--   The structure `DeligneDatum π B`, abbreviated `OmegaObj`, consists of: a $B$-submodule $N_M \subset B \otimes_{\mathcal{O}} M$ for every full lattice $M$ (the field `line`); a proof field asserting that each quotient $(B\otimes_{\mathcal{O}} M)/N_M$ is an invertible $B$-module; monotonicity, that for $M' \le M$ the image of $N_{M'}$ in $B \otimes_{\mathcal{O}} M$ lies in $N_M$; homothety equivariance, $N_{cM} = (1\otimes c)(N_M)$ for $c \in K^{\times}$, via the scalar matrix `scalarGL c`; and a non-degeneracy field, requiring for every prime ideal $\mathfrak{p} \subset B$ lattices $M' \le M$ with $\pi M \subseteq M'$ such that $1 \otimes v \notin N_M + \mathfrak{p}(B\otimes M)$ for all $v \in M \setminus M'$, and $1 \otimes v' \notin N_{M'} + \mathfrak{p}(B\otimes M')$ for all $v' \in M'$ not of the form $\pi w$ with $w \in M$. By `ext'` a datum is determined by its family of submodules.
--
--   Two relations are recorded as predicates on pairs of data: `IsPullback g d d'`, that $N'_M$ is the preimage of $N_{gM}$ under $1 \otimes g$ for all $M$; and `IsBaseChange f d d'` along an $\mathcal{O}$-algebra map $f : B \to B'$, that $N'_M$ is the $B'$-span of the image of $N_M$ under $f \otimes \mathrm{id}_M$ (`lineBaseChange`). Finally, given an $\mathcal{O}$-algebra $\mathcal{O}^{\mathrm{nr}}$ with an $\mathcal{O}$-algebra automorphism $\mathrm{Fr}$ and a homomorphism $\mathrm{vdet} : \mathrm{GL}_2(K) \to \mathbb{Z}$, `OmegaNrObj B` is the product of $\mathrm{Hom}_{\mathcal{O}\text{-alg}}(\mathcal{O}^{\mathrm{nr}}, B)$ with `OmegaObj π B`, `frobTwist n ψ` is $\psi \circ \mathrm{Fr}^{n}$, and `OmegaNr.IsTwistedAct B g x x'` asserts that the first component of $x'$ is the $\mathrm{Fr}^{-\mathrm{vdet}(g)}$-twist of that of $x$ while the second components are related by `IsPullback` for $g^{-1}$.
--
--   **Relation to Mathlib.** Mathlib has no formal upper half plane or Deligne lattice datum; these are the project's own notions, phrased with Mathlib's tensor products, `Submodule.baseChange`, `Module.Invertible` and `Matrix.GeneralLinearGroup`.
--
--   **Where it is used.** These data are the pointwise description of the formal upper half plane $\widehat{\Omega}$ as a functor on $\mathcal{O}$-algebras, indexed by the lattices attached to the Bruhat–Tits tree, together with its $\mathrm{GL}_2(K)$-action twisted by the unramified coefficients; they underlie the $p$-adic uniformisation of Shimura curves used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum.lean

import Mathlib
import Definitions.Def_LatticeTreeOrbital
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree

namespace CerednikDrinfeld
namespace FormalOmega

section Datum

variable (𝒪 : Type) [CommRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] (π : 𝒪)

abbrev latticeBaseChange (B : Type) [CommRing B] [Algebra 𝒪 B] (M : FullLattice 𝒪 K) : Type :=
  B ⊗[𝒪] ↥M.1

variable {𝒪 K}

noncomputable def inclBaseChange (B : Type) [CommRing B] [Algebra 𝒪 B] {M' M : FullLattice 𝒪 K} (h : M'.1 ≤ M.1) :
    latticeBaseChange 𝒪 K B M' →ₗ[B] latticeBaseChange 𝒪 K B M :=
  (Submodule.inclusion h).baseChange B

theorem mulVecLinR_injective (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Function.Injective (mulVecLinR (R := 𝒪) g) := by
  intro v w hvw
  have h := congrArg (fun x => Matrix.mulVec ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) x) hvw
  simpa only [mulVecLinR_apply, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec] using h

noncomputable def latticeMapEquiv (g : Matrix.GeneralLinearGroup (Fin 2) K) (M : Submodule 𝒪 (Fin 2 → K)) :
    ↥M ≃ₗ[𝒪] ↥(latticeMap g M) :=
  Submodule.equivMapOfInjective (mulVecLinR (R := 𝒪) g) (mulVecLinR_injective g) M

def FullLattice.act (g : Matrix.GeneralLinearGroup (Fin 2) K) (M : FullLattice 𝒪 K) : FullLattice 𝒪 K :=
  ⟨latticeMap g M.1, M.2.map g⟩

noncomputable def actBaseChange (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (M : FullLattice 𝒪 K) : latticeBaseChange 𝒪 K B M ≃ₗ[B] latticeBaseChange 𝒪 K B (FullLattice.act g M) :=
  (latticeMapEquiv g M.1).baseChange 𝒪 B _ _

structure DeligneDatum (B : Type) [CommRing B] [Algebra 𝒪 B] : Type where

  line : ∀ M : FullLattice 𝒪 K, Submodule B (latticeBaseChange 𝒪 K B M)

  invertible : ∀ M : FullLattice 𝒪 K, Module.Invertible B (latticeBaseChange 𝒪 K B M ⧸ line M)

  mono : ∀ {M' M : FullLattice 𝒪 K} (h : M'.1 ≤ M.1), (line M').map (inclBaseChange B h) ≤ line M

  homothety : ∀ (c : Kˣ) (M : FullLattice 𝒪 K),
    line (FullLattice.act (scalarGL c) M) = (line M).map (actBaseChange B (scalarGL c) M).toLinearMap

  nondeg : ∀ (𝔭 : Ideal B), 𝔭.IsPrime →
    ∃ (M' M : FullLattice 𝒪 K) (_ : M'.1 ≤ M.1),
      (∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1) ∧
      (∀ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1 →
        (1 : B) ⊗ₜ[𝒪] v ∉ line M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) ∧
      (∀ v' : ↥M'.1, (¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) →
        (1 : B) ⊗ₜ[𝒪] v' ∉ line M' ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M')))

namespace DeligneDatum

variable {π}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem ext' {d d' : DeligneDatum (K := K) π B} (h : d.line = d'.line) : d = d' := by
  cases d; cases d'; cases h; rfl

end DeligneDatum

abbrev OmegaObj (B : Type) [CommRing B] [Algebra 𝒪 B] : Type := DeligneDatum (K := K) π B

variable (B : Type) [CommRing B] [Algebra 𝒪 B]

def DeligneDatum.IsPullback (g : Matrix.GeneralLinearGroup (Fin 2) K) (d d' : DeligneDatum (K := K) π B) : Prop :=
  ∀ M : FullLattice 𝒪 K, d'.line M = (d.line (FullLattice.act g M)).comap (actBaseChange B g M).toLinearMap

variable {B}

noncomputable def lineBaseChange {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B') (M : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) : Submodule B' (latticeBaseChange 𝒪 K B' M) :=
  Submodule.span B' ((LinearMap.rTensor (↥M.1) f.toLinearMap) '' (N : Set (latticeBaseChange 𝒪 K B M)))

def DeligneDatum.IsBaseChange {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    (d : DeligneDatum (K := K) π B) (d' : DeligneDatum (K := K) π B') : Prop :=
  ∀ M : FullLattice 𝒪 K, d'.line M = lineBaseChange f M (d.line M)

end Datum

section OmegaNr

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
variable (vdet : Matrix.GeneralLinearGroup (Fin 2) K →* Multiplicative ℤ)

abbrev OmegaNrObj (B : Type) [CommRing B] [Algebra 𝒪 B] : Type :=
  (Onr →ₐ[𝒪] B) × OmegaObj (K := K) π B

noncomputable def frobTwist (n : ℤ) {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) : Onr →ₐ[𝒪] B :=
  ψ.comp ((Fr ^ n : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr)

def OmegaNr.IsTwistedAct (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (x x' : OmegaNrObj (K := K) π Onr B) : Prop :=
  x'.1 = frobTwist Onr Fr (- Multiplicative.toAdd (vdet g)) x.1 ∧
    DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ x.2 x'.2

end OmegaNr

end FormalOmega
end CerednikDrinfeld


