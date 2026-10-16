-- Prove2me | Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
-- name    : OAI_InformationTheory_PhotonNumber_Generator
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T23:24:47.671638+00:00
-- url     : https://prove2.me/theorems/e049c969-66d0-4526-aca3-91885cbe3f77
-- title:
--   Weighted-column ensembles of a state and the physical thermal-noise generator on Fock space
-- statement:
--   This file packages a state as an ensemble of number-weighted vectors and defines, in terms of such ensembles, the thermal-noise generator, its single-port weak form, and the conditional ("slice") maps obtained by sending one input through a beam splitter.
--
--   Notation: $\mathcal F_n = \ell^2(\mathbb{N}^n)$ is the $n$-mode Fock space, $\nu(k) = 1+\sum_jk_j$, $W_m$ multiplies the $k$-th coordinate by $\nu(k)^{-m}$, $e_j$ is the $j$-th unit vector, and for families $u,v$ of vectors $O(u,v) = \sum_i|u_i\rangle\langle v_i|$ and $\Pi(u,v;Z) = \sum_i\langle v_i,Zu_i\rangle$. A state is a positive operator $\rho$ on $\mathcal F_n$ with $\sum_k\operatorname{Re}\langle k|\rho|k\rangle = 1$.
--
--   1. **Coefficients and families.** For a mode $j$: $\sqrt{k_j+1}$ (lowering), $\sqrt{k_j}$ (raising, $0$ if $k_j=0$) and $k_j+[u]$ for a direction $u$ (mode coefficient). For a family $(x_i)$ in $\mathcal F_n$, the lowered, raised, mode and base families are
--   $$
--   (A_jx_i)_k = \frac{\sqrt{k_j+1}}{\nu(k+e_j)^3}\,(x_i)_{k+e_j},\quad (C_jx_i)_{k+e_j} = \frac{\sqrt{k_j+1}}{\nu(k)^3}\,(x_i)_k,\quad (M^u_jx_i)_k = \frac{k_j+[u]}{\nu(k)^3}(x_i)_k,\quad W_3x_i,
--   $$
--   with $(C_jx_i)_k = 0$ when $k_j = 0$; thus $A_jx_i$, $C_jx_i$ and $M^u_jx_i$ are the annihilation, creation and number-type operators applied to $W_3x_i$.
--
--   2. **The physical generator.** For a direction $u$ (lowering $-$ or raising $+$) the dissipator is
--   $$
--   D^u_j(x) = O(F^u_jx,F^u_jx) - \tfrac12\bigl(O(M^u_jx, W_3x) + O(W_3x, M^u_jx)\bigr),\qquad F^-_j = A_j,\ F^+_j = C_j,
--   $$
--   and for $r\in\mathbb{R}$ the generator is $\mathcal L_r(x) = \sum_{j=1}^n\bigl((r+1)D^-_j(x) + r\,D^+_j(x)\bigr)$. Writing $\rho = O(W_3x,W_3x)$, the terms $O(A_jx,A_jx)$, $O(C_jx,C_jx)$, $O(M^-_jx,W_3x)$ and $O(M^+_jx,W_3x)$ correspond formally to $a_j\rho a_j^\dagger$, $a_j^\dagger\rho a_j$, $a_j^\dagger a_j\rho$ and $a_ja_j^\dagger\rho$, so that $\mathcal L_r$ is a bounded-operator form of the thermal-noise Lindbladian $\sum_j(r+1)\bigl(a_j\rho a_j^\dagger-\tfrac12\{a_j^\dagger a_j,\rho\}\bigr) + r\bigl(a_j^\dagger\rho a_j-\tfrac12\{a_ja_j^\dagger,\rho\}\bigr)$. The weak operator is $(r+1)\,O(W_3x,A_jx) - r\,O(C_jx,W_3x)$.
--
--   3. **Weighted columns of a state.** A weighted-column representation of a state $\rho$ consists of an index set and vectors $(x_i)$ in $\mathcal F_n$ with $\sum_i\|x_i\|^2<\infty$, $\sum_i\|W_3x_i\|^2 = 1$, and
--   $$
--   \sum_i |W_3x_i\rangle\langle W_3x_i| = \rho .
--   $$
--
--   4. **Slices through a beam splitter.** Given such a representation and $\eta\in[0,1]$: the slice of an operator $B$ is the weighted conditional $\sum_iV_{i}^*(B\otimes1)V_{i}$ along the ratio-weighted beam columns $V_i(x) = \theta^2\,\mathcal U_\eta\,\tau^2\,(x\otimes W_1x_i)$ (where $\mathcal U_\eta$ is the beam-splitter unitary and $\tau^2$, $\theta^2$ are the diagonal operators with entries $\bigl(W(k,e)/(\nu(k)\nu(e))\bigr)^2$ and $\bigl(\nu(k)/W(k,e)\bigr)^2$, $W(k,e) = \nu(k)+\nu(e)-1$); the right slice uses $W_1x_i\otimes x$ instead. The raw slice of an operator $Z$ is the conditional map of $\mathcal U_\eta^{-1}(Z\otimes1)\mathcal U_\eta$ along the normalised family $(W_3x_i)$, i.e. the operator characterised by
--   $$
--   \langle u,\ \mathrm{raw}(Z)\,v\rangle = \sum_i\bigl\langle u\otimes W_3x_i,\ \mathcal U_\eta^{-1}(Z\otimes1)\,\mathcal U_\eta\,(v\otimes W_3x_i)\bigr\rangle,
--   $$
--   with the right raw slice placing $W_3x_i$ in the first factor.
--
--   5. **Weak means.** The expectation of $Z$ is $\mathbb E(Z) = \sum_i\langle W_3x_i,ZW_3x_i\rangle$. With the single-port weak form $\Omega_{r,j}(Z) = (r+1)\sum_i\langle A_jx_i, Z\,W_3x_i\rangle - r\sum_i\langle W_3x_i, Z\,C_jx_i\rangle$, the weak mean is $\Omega_{r,j}(1)$ and the centered weak form is $\Omega_{r,j}(Z) - \Omega_{r,j}(1)\,\mathbb E(Z)$.
--
--   These objects express the time derivative of a state under thermal noise, and the effect of the beam splitter on one input, entirely through bounded operators applied to a square-summable ensemble, so that they can be handled on the untruncated Fock space.
--
--   **Formalization Note** The representation is the structure `WeightedColumns ρ` (fields `Index`, `vector`, `summable`, `normalized`, `density`). $O$ and $\Pi$ are `tsum`s (zero for divergent series). The slices take `hη : η ∈ Set.Icc 0 1`; the raw slices use `conditionalLeft`/`conditionalRight` of the conjugated lift `conjugate η hη Z`. Directions are encoded by `Bool`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Generator.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Generator.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntropyPhotonNumber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal

namespace PhysicalGenerator
open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I : Type*}

def lowerCoefficient (j : Fin n) (k : NumberIndex n) : ℂ := Real.sqrt ((k j:ℝ)+1)
def raiseCoefficient (j : Fin n) (k : NumberIndex n) : ℂ :=
  if k j=0 then 0 else Real.sqrt (k j:ℝ)
def modeCoefficient (j : Fin n) (u : Bool) (k : NumberIndex n) : ℂ :=
  (k j:ℂ)+(if u then 1 else 0)

def lowerFamily (j : Fin n) (x : I → Fock n) := fun i => sandwich 0 3 (by omega) j (x i)
def raiseFamily (j : Fin n) (x : I → Fock n) := fun i => creationSandwich 0 3 (by omega) j (x i)
def modeFamily (j : Fin n) (u : Bool) (x : I → Fock n) := fun i => inverseWeight 2 (modeBound j u (x i))
def baseFamily (x : I → Fock n) := fun i => inverseWeight 3 (x i)

def dissipator (j : Fin n) (u : Bool) (x : I → Fock n) : Fock n →L[ℂ] Fock n :=
  CrossEnsemble.operator (if u then raiseFamily j x else lowerFamily j x)
      (if u then raiseFamily j x else lowerFamily j x)-
    (2:ℂ)⁻¹ • (CrossEnsemble.operator (modeFamily j u x) (baseFamily x)+
      CrossEnsemble.operator (baseFamily x) (modeFamily j u x))
def generator (r : ℝ) (x : I → Fock n) : Fock n →L[ℂ] Fock n :=
  ∑ j, (((r+1:ℝ):ℂ) • dissipator j false x+(r:ℂ) • dissipator j true x)

end PhysicalGenerator

namespace QuantumTrace
end QuantumTrace

namespace PhysicalGenerator

section
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ} {I : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I J K : Type*}

end PhysicalGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder

structure WeightedColumns {n : ℕ} (ρ : State n) where
  Index : Type
  vector : Index → Fock n
  summable : Summable (fun i => ‖vector i‖^2)
  normalized : HasSum (fun i => ‖inverseWeight 3 (vector i)‖^2) 1
  density : TraceEnsemble.operator (fun i => inverseWeight 3 (vector i))=ρ.op

namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

def slice (η : ℝ) (hη : η ∈ Set.Icc 0 1) (B : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  weightedConditional η hη (fun i => inverseWeight 1 (X.vector i)) B

def sliceRight (η : ℝ) (hη : η ∈ Set.Icc 0 1) (B : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  weightedConditionalRight η hη (fun i => inverseWeight 1 (X.vector i)) B

end WeightedColumns

end EntropyPhotonNumber

namespace PhysicalGenerator
open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I J K : Type*}

def weakOperator (r : ℝ) (j : Fin n) (x : I → Fock n) : Fock n →L[ℂ] Fock n :=
  (r+1:ℂ) • CrossEnsemble.operator (baseFamily x) (lowerFamily j x)-
    (r:ℂ) • CrossEnsemble.operator (raiseFamily j x) (baseFamily x)

end PhysicalGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder TensorLp
namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

def rawSlice (η : ℝ) (hη : η ∈ Set.Icc 0 1) (Z : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  conditionalLeft (fun i => inverseWeight 3 (X.vector i)) X.normalized (conjugate η hη Z)

def rawSliceRight (η : ℝ) (hη : η ∈ Set.Icc 0 1) (Z : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  conditionalRight (fun i => inverseWeight 3 (X.vector i)) X.normalized (conjugate η hη Z)

end WeightedColumns

end EntropyPhotonNumber

namespace KrausBounded
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
end KrausBounded

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}
end BeamLadder

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder TensorLp
namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

def expectation (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  CrossEnsemble.pairing (fun i => inverseWeight 3 (X.vector i))
    (fun i => inverseWeight 3 (X.vector i)) Z

def weakMean (r : ℝ) (j : Fin n) : ℂ := singleWeak r j X.vector 1

def centeredWeak (r : ℝ) (j : Fin n) (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  singleWeak r j X.vector Z-X.weakMean r j*X.expectation Z

end WeightedColumns

end EntropyPhotonNumber

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

end BeamLadder

namespace EntropyPhotonNumber

namespace WeightedColumns
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

end WeightedColumns

end EntropyPhotonNumber

end

end OAI


