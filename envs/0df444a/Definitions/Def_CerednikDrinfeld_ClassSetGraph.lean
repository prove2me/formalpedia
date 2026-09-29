-- Prove2me | Definitions.Def_CerednikDrinfeld_ClassSetGraph
-- name    : CerednikDrinfeld_ClassSetGraph
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/03fd934c-3166-54ae-9632-6a7beef22923
-- title:
--   Class sets, Hecke matrices and degeneracy data on quaternion class sets
-- statement:
--   Throughout, $a,b\in\mathbb{Q}$ and $\mathbb{H}=\mathbb{H}[\mathbb{Q},a,b]$; for an open-ish subgroup $U\le(\mathbb{H}\otimes_\mathbb{Q}\mathbb{A}_f)^\times$ the class set `ClassSet U` is the double coset quotient of $(\mathbb{H}\otimes_{\mathbb{Q}}\mathbb{A}_f)^\times$ by the image of the diagonal $\mathbb{H}^\times$ on the left and $U$ on the right, and `x.out` denotes a chosen representative idele of a class $x$. For a $\mathbb{Z}$-submodule $R\subseteq\mathbb{H}$ and an idele $n$, `meetOrder R n` is the intersection $R\cap\mathrm{conjByFiniteIdele}(R,n)$, the latter being the lattice of elements of $\mathbb{H}$ whose image under $z\mapsto z\otimes 1$ lies in $n\,\widehat{R}\,n^{-1}$, where $\widehat{R}$ is the adelic box of $R$. The helpers `classSetForget` and `classSetShift` send a class to the class of its chosen representative for another group $U'$, resp. to the class of $x_{\mathrm{out}}\,n$. Weights are arithmetic: `unitWeight Λ` is the cardinality of $\{u: \mathrm{IsUnitOf}\ \Lambda\ u\}$ divided by $2$ in natural division and sent into $\mathbb{N}^{+}$ (so the value $0$ becomes $1$), and `classWeight U Λ x` is `unitWeight` of $\mathrm{conjByFiniteIdele}(\Lambda,x_{\mathrm{out}})$. `classSetHeckeMatrix U T` is the integer matrix whose $(i,j)$ entry is $\mathrm{heckeKernel}\,U\,T\,j\,i$, i.e. the number of cosets $hU$ with $h\in T$ and $[x_{j,\mathrm{out}}h]=i$ — the transpose of the incidence kernel. Two Hecke sets cut out of the $\ell$-th prime Hecke set are defined: `uHeckeSet R n q`, the $h\in\mathrm{primeHeckeSet}(\mathrm{meetOrder}\,R\,n)\,q$ with $h$ conjugating $n\widehat R n^{-1}$ to $\widehat R$ and $h\widehat R h^{-1}\neq n\widehat R n^{-1}$; and `levelHeckeUSet Λ O ℓ`, the $h\in\mathrm{primeHeckeSet}\,O\,\ell$ with $h\widehat O h^{-1}\neq\widehat O$ and $\widehat O\not\le h\widehat\Lambda h^{-1}$. From these, `classSetDegeneracyData R n` packages the two maps `ClassSet (stabiliser (meetOrder R n)) → ClassSet (stabiliser R)`, namely $x\mapsto[x_{\mathrm{out}}]$ and $x\mapsto[x_{\mathrm{out}}n]$, together with the weight function `classWeight`; `classSetEdgeHecke N q Λ R n ℓ` and `classSetVertexHecke N Λ R ℓ` are the corresponding Hecke matrices, chosen by a three-way case split ($\ell=q$, $\ell\mid N$, else) resp. a two-way split. Finally `ClassSetHeckeLaws` is the conjunction of four assertions — commutation of the edge matrices among themselves, of the vertex matrices among themselves, compatibility of the edge matrices with both degeneracy pushforwards for $\ell\neq q$, and stability of the joint kernel — and `classSetHeckeData` is a total `HeckeData` structure over `classSetDegeneracyData R n` with bad set $\{q\}$: it uses the above matrices when `ClassSetHeckeLaws` holds, and the zero matrices otherwise.
--
--   **Relation to Mathlib.** Built on Mathlib's rational quaternion algebras, finite adele rings and double coset quotients; Mathlib has no notion of quaternionic class sets, adelic Hecke correspondences or the degeneracy/Hecke data structures used here, which are the project's own.
--
--   **Where it is used.** These data feed the Čerednik–Drinfeld description of the component group of the Jacobian of a Shimura curve in terms of class sets of Eichler orders in a definite quaternion algebra, with the edge and vertex Hecke matrices modelling the action on the dual graph; this component-group input is what drives the level-lowering step for the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_ClassSetGraph.lean

import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_Ribbon

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

noncomputable section

namespace CerednikDrinfeld

variable {a b : ℚ}

def meetOrder (R : Submodule ℤ ℍ[ℚ, a, b]) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Submodule ℤ ℍ[ℚ, a, b] :=
  R ⊓ Submodule.conjByFiniteIdele R n

def classSetForget (U U' : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (x : ClassSet U) :
    ClassSet U' :=
  ClassSet.mk U' x.out

def classSetShift (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (x : ClassSet U) : ClassSet U :=
  ClassSet.mk U (x.out * n)

def unitWeight (Λ : Submodule ℤ ℍ[ℚ, a, b]) : ℕ+ :=
  Nat.toPNat' (Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf Λ u} / 2)

def classWeight (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (x : ClassSet U) : ℕ+ :=
  unitWeight (Submodule.conjByFiniteIdele Λ x.out)

def classSetHeckeMatrix (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (T : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Matrix (ClassSet U) (ClassSet U) ℤ :=
  Matrix.of fun i j => heckeKernel U T j i

def uHeckeSet (R : Submodule ℤ ℍ[ℚ, a, b]) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (q : ℕ) :
    Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  {h | h ∈ primeHeckeSet (meetOrder R n) q ∧
    Submodule.conjByFiniteIdele (Submodule.conjByFiniteIdele R n) h = R ∧
    Submodule.conjByFiniteIdele R h ≠ Submodule.conjByFiniteIdele R n}

def levelHeckeUSet (Λ O : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) :
    Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  {h | h ∈ primeHeckeSet O ℓ ∧ Submodule.conjByFiniteIdele O h ≠ O ∧ ¬ O ≤ Submodule.conjByFiniteIdele Λ h}

def classSetDegeneracyData (R : Submodule ℤ ℍ[ℚ, a, b]) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    DegeneracyData (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))
      (ClassSet (Submodule.finiteIdeleStabilizer R)) where
  a := classSetForget _ _
  b x := ClassSet.mk _ (x.out * n)
  w := classWeight _ (meetOrder R n)

def classSetEdgeHecke (N q : ℕ) (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ℓ : Nat.Primes) :
    Matrix (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))
      (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n))) ℤ :=
  if (ℓ : ℕ) = q then classSetHeckeMatrix _ (uHeckeSet R n q)
  else if (ℓ : ℕ) ∣ N then classSetHeckeMatrix _ (levelHeckeUSet Λ (meetOrder R n) ℓ)
  else classSetHeckeMatrix _ (primeHeckeSet (meetOrder R n) ℓ)

def classSetVertexHecke (N : ℕ) (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : Nat.Primes) :
    Matrix (ClassSet (Submodule.finiteIdeleStabilizer R)) (ClassSet (Submodule.finiteIdeleStabilizer R)) ℤ :=
  if (ℓ : ℕ) ∣ N then classSetHeckeMatrix _ (levelHeckeUSet Λ R ℓ)
  else classSetHeckeMatrix _ (primeHeckeSet R ℓ)

section Laws

variable (N q : ℕ) [Fact q.Prime] (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
  [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
  [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
  [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]

def ClassSetHeckeLaws : Prop :=
  (∀ ℓ ℓ' : Nat.Primes, Commute (classSetEdgeHecke N q Λ R n ℓ) (classSetEdgeHecke N q Λ R n ℓ')) ∧
  (∀ ℓ ℓ' : Nat.Primes, Commute (classSetVertexHecke N Λ R ℓ) (classSetVertexHecke N Λ R ℓ')) ∧
  (∀ ℓ : Nat.Primes, ℓ ∉ ({⟨q, Fact.out⟩} : Finset Nat.Primes) → ∀ i : Fin 2,
    ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ,
      jointDelta (classSetDegeneracyData R n) i ((classSetEdgeHecke N q Λ R n ℓ).mulVecLin x) =
        (classSetVertexHecke N Λ R ℓ).mulVecLin (jointDelta (classSetDegeneracyData R n) i x)) ∧
  (∀ ℓ : Nat.Primes, ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ,
    (∀ i, jointDelta (classSetDegeneracyData R n) i x = 0) →
      ∀ i, jointDelta (classSetDegeneracyData R n) i ((classSetEdgeHecke N q Λ R n ℓ).mulVecLin x) = 0)

open Classical in

def classSetHeckeData : HeckeData (classSetDegeneracyData R n) :=
  if h : ClassSetHeckeLaws N q Λ R n then
    { T := classSetEdgeHecke N q Λ R n
      Tv := classSetVertexHecke N Λ R
      comm := h.1
      commv := h.2.1
      S := {⟨q, Fact.out⟩}
      good_equivariant := h.2.2.1
      kernel_stable := h.2.2.2 }
  else
    { T := 0
      Tv := 0
      comm := fun _ _ => Commute.refl 0
      commv := fun _ _ => Commute.refl 0
      S := {⟨q, Fact.out⟩}
      good_equivariant := fun _ _ i x => by
        simp only [Pi.zero_apply, LinearMap.zero_apply, map_zero]
      kernel_stable := fun _ x _ i => by
        simp only [Pi.zero_apply, LinearMap.zero_apply, map_zero] }

end Laws

end CerednikDrinfeld

end


