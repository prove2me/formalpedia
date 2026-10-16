-- Prove2me | Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
-- name    : OAI_InformationTheory_PhotonNumber_BeamForms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T23:23:50.399448+00:00
-- url     : https://prove2.me/theorems/4f3d9773-323f-4f5b-afd4-d496deeed0ae
-- title:
--   Two-port generator forms, ratio-weighted beam columns and pushed-forward dissipators
-- statement:
--   This file defines the bilinear forms that describe a thermal-noise generator acting on one port of a two-port bosonic system, and the number-weighted beam-splitter "columns" that transport ensembles from one input port to the output port.
--
--   Notation: $\mathcal F_n = \ell^2(\mathbb{N}^n)$ with $\nu(k) = 1+\sum_jk_j$ and $W_m$ the diagonal operator with entries $\nu(k)^{-m}$; the joint space $\ell^2(\mathbb{N}^n\times\mathbb{N}^n)$ carries the joint weight $W(k,e) = \nu(k)+\nu(e)-1$ and the diagonal operator $W^{-1}$ multiplying by $W(k,e)^{-1}$. On the joint space, $L^A_j$, $L^B_j$ are the bounded lowering operators $(L^A_jx)(k,e) = \sqrt{k_j+1}\,x(k+e_j,e)/(W(k,e)+1)$ (and similarly on the second port), and $R^A_j = \phi(W)(L^A_j)^*$, $R^B_j = \phi(W)(L^B_j)^*$ with $\phi(w) = w/(w-1)$ for $w>1$, $\phi(w)=0$ otherwise. $\mathcal U_\eta$ ($\eta\in[0,1]$) is the beam-splitter unitary, and $\Pi(u,v;Z) = \sum_i\langle v_i,Zu_i\rangle$, $O(u,v) = \sum_i|u_i\rangle\langle v_i|$ for families $u,v$.
--
--   1. **Pre-ladders and quadratic forms.** Put $\tilde L^A_j = L^A_j(1-W^{-1})$ and $\tilde R^A_j = R^A_j(1+W^{-1})$ (similarly for port $B$). For joint vectors $x,y$ and an operator $Z$,
--   $$
--   q^-_{A,j}(x,y;Z) = \langle L^A_jW^{-1}x, Z\,L^A_jW^{-1}y\rangle - \tfrac12\bigl(\langle W^{-2}x, Z\,R^A_j\tilde L^A_jy\rangle + \langle R^A_j\tilde L^A_jx, Z\,W^{-2}y\rangle\bigr),
--   $$
--   and $q^+_{A,j}$ is the same with the roles of $L^A_j$ and $R^A_j$ exchanged (using $\tilde R^A_j$); $q^\pm_{B,j}$ are defined likewise. The cross forms $c^\mp_j(x,y;T)$ are the analogous expressions mixing the two ports: for example $c^-_j = \langle L^A_jW^{-1}x, TL^B_jW^{-1}y\rangle + \langle L^B_jW^{-1}x, TL^A_jW^{-1}y\rangle - \tfrac12\bigl(\langle W^{-2}x, T(R^A_j\tilde L^B_j + R^B_j\tilde L^A_j)y\rangle + \langle (R^A_j\tilde L^B_j + R^B_j\tilde L^A_j)x, TW^{-2}y\rangle\bigr)$, and $c^+_j$ exchanges lowering and raising.
--
--   2. **Generator pairings.** For $r\in\mathbb{R}$ and families $(x_i)$, $(y_i)$ of joint vectors,
--   $$
--   \mathcal G_A(r;x,y;Z) = \sum_{j=1}^n\Bigl((r+1)\sum_iq^-_{A,j}(x_i,y_i;Z) + r\sum_iq^+_{A,j}(x_i,y_i;Z)\Bigr),
--   $$
--   and $\mathcal G_B$ likewise. On a single port, for a family $(x_i)$ in $\mathcal F_n$, the pairing is $\sum_j\bigl[(r+1)\bigl(\Pi(Ax,Ax;Z)-\tfrac12(\Pi(W_2B^-_jx,W_3x;Z)+\Pi(W_3x,W_2B^-_jx;Z))\bigr) + r\bigl(\Pi(Cx,Cx;Z)-\tfrac12(\Pi(W_2B^+_jx,W_3x;Z)+\Pi(W_3x,W_2B^+_jx;Z))\bigr)\bigr]$, where $(Ax)_k = \sqrt{k_j+1}\,\nu(k+e_j)^{-3}x_{k+e_j}$, $(Cx)_{k+e_j} = \sqrt{k_j+1}\,\nu(k)^{-3}x_k$ (zero where $k_j=0$), and $B^\pm_j$ is diagonal with entries $(k_j+[\pm=+])/\nu(k)$. A second tensor preimage is $W_1x\otimes W_3y + W_3x\otimes W_1y + W_3x\otimes W_3y + 2W_2x\otimes W_2y - 2W_2x\otimes W_3y - 2W_3x\otimes W_2y$.
--
--   3. **Ratio-weighted beam columns.** The tensor ratio $\tau(k,e) = W(k,e)/(\nu(k)\nu(e))$ and the retained ratio $\theta(k,e) = \nu(k)/W(k,e)$ both lie in $[0,1]$, so multiplication by $\tau^2$ and by $\theta^2$ are bounded operators of norm at most $1$. For $\eta\in[0,1]$ and $y\in\mathcal F_n$ the weighted columns are the bounded maps $\mathcal F_n\to\ell^2(\mathbb{N}^n\times\mathbb{N}^n)$
--   $$
--   V_y(x) = \theta^2\,\mathcal U_\eta\,\tau^2\,(x\otimes y),\qquad V'_y(x) = \theta^2\,\mathcal U_\eta\,\tau^2\,(y\otimes x).
--   $$
--
--   4. **Pullbacks and conditionals.** For bounded $V:E\to F$ and $Z$ on $F$, the compression is $V^*ZV$, and the pullback along a family $(V_i)$ is $\sum_iV_i^*ZV_i$. The weighted conditional of an operator $B$ on $\mathcal F_n$ along a family $(y_j)$ is $\sum_jV_{y_j}^*(B\otimes1)V_{y_j}$ (with $V'$ for the right version), and the weighted slices of families $(x_i)$, $(y_j)$ are the vectors $\bigl(V_{y_j}(x_i)\bigr)_e\in\mathcal F_n$, the slices at second index $e\in\mathbb{N}^n$ (again also with $V'$).
--
--   5. **Pushed generators.** Given any map $F$ sending families indexed by $I$ to families indexed by $K$, the pushed dissipator and generator are the weighted generator of the Fock-space operators with each family replaced by its image: $D^\sigma_j = O(F(G^\sigma_jx),F(G^\sigma_jx)) - \tfrac12\bigl(O(F(B^\sigma_jx),F(W_1x)) + O(F(W_1x),F(B^\sigma_jx))\bigr)$ and $\sum_j\bigl((r+1)D^-_j + rD^+_j\bigr)$, where $G^-_jx = (\nu(k)^2\sqrt{k_j+1}\,\nu(k+e_j)^{-3}x_{k+e_j})_k$ and $G^+_j$ is its raising analogue; the pushed pairing replaces each $O$ by $\Pi(\,\cdot\,,\,\cdot\,;Z)$.
--
--   These forms are designed as weak (quadratic-form) versions of the noise generator acting on each port, written so that every operator involved is bounded on the untruncated Fock spaces; the weighted columns move an ensemble on one input through the beam splitter while keeping track of the number weights.
--
--   **Formalization Note** The forms are named `quadMinusL`, `quadPlusL`, `crossMinus`, `crossPlus`, `generatorPairingL`, `singleGeneratorPairing`; the columns are `weightedColumn` and `weightedColumnRight`, and the pullback is a `tsum` (so it is $0$ if the series of compressions does not converge). Directions of the mode index are encoded by `Bool`. `beamUnitary η hη` needs `hη : η ∈ Set.Icc 0 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/BeamForms.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/BeamForms.lean by skeleton subtraction
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

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

def preLowerL (j : Fin n) : JointFock n →L[ℂ] JointFock n := lowerL j ∘L (1-inverse)
def preLowerR (j : Fin n) : JointFock n →L[ℂ] JointFock n := lowerR j ∘L (1-inverse)
def preRaiseL (j : Fin n) : JointFock n →L[ℂ] JointFock n := raiseL j ∘L (1+inverse)
def preRaiseR (j : Fin n) : JointFock n →L[ℂ] JointFock n := raiseR j ∘L (1+inverse)

def quadMinusL (j : Fin n) (x y : JointFock n) (Z : JointFock n →L[ℂ] JointFock n) : ℂ :=
  inner ℂ (lowerL j (inverse x)) (Z (lowerL j (inverse y)))-
    (2:ℂ)⁻¹*(inner ℂ (inverse (inverse x)) (Z (raiseL j (preLowerL j y)))+
      inner ℂ (raiseL j (preLowerL j x)) (Z (inverse (inverse y))))
def quadMinusR (j : Fin n) (x y : JointFock n) (Z : JointFock n →L[ℂ] JointFock n) : ℂ :=
  inner ℂ (lowerR j (inverse x)) (Z (lowerR j (inverse y)))-
    (2:ℂ)⁻¹*(inner ℂ (inverse (inverse x)) (Z (raiseR j (preLowerR j y)))+
      inner ℂ (raiseR j (preLowerR j x)) (Z (inverse (inverse y))))
def quadPlusL (j : Fin n) (x y : JointFock n) (Z : JointFock n →L[ℂ] JointFock n) : ℂ :=
  inner ℂ (raiseL j (inverse x)) (Z (raiseL j (inverse y)))-
    (2:ℂ)⁻¹*(inner ℂ (inverse (inverse x)) (Z (lowerL j (preRaiseL j y)))+
      inner ℂ (lowerL j (preRaiseL j x)) (Z (inverse (inverse y))))
def quadPlusR (j : Fin n) (x y : JointFock n) (Z : JointFock n →L[ℂ] JointFock n) : ℂ :=
  inner ℂ (raiseR j (inverse x)) (Z (raiseR j (inverse y)))-
    (2:ℂ)⁻¹*(inner ℂ (inverse (inverse x)) (Z (lowerR j (preRaiseR j y)))+
      inner ℂ (lowerR j (preRaiseR j x)) (Z (inverse (inverse y))))

def crossMinus (j : Fin n) (x y : JointFock n) (T : JointFock n →L[ℂ] JointFock n) : ℂ :=
  inner ℂ (lowerL j (inverse x)) (T (lowerR j (inverse y)))+
  inner ℂ (lowerR j (inverse x)) (T (lowerL j (inverse y)))-
  (2:ℂ)⁻¹*(inner ℂ (inverse (inverse x)) (T (raiseL j (preLowerR j y)))+
    inner ℂ (inverse (inverse x)) (T (raiseR j (preLowerL j y)))+
    inner ℂ (raiseL j (preLowerR j x)) (T (inverse (inverse y)))+
    inner ℂ (raiseR j (preLowerL j x)) (T (inverse (inverse y))))

def crossPlus (j : Fin n) (x y : JointFock n) (T : JointFock n →L[ℂ] JointFock n) : ℂ :=
  inner ℂ (raiseL j (inverse x)) (T (raiseR j (inverse y)))+
  inner ℂ (raiseR j (inverse x)) (T (raiseL j (inverse y)))-
  (2:ℂ)⁻¹*(inner ℂ (inverse (inverse x)) (T (lowerL j (preRaiseR j y)))+
    inner ℂ (inverse (inverse x)) (T (lowerR j (preRaiseL j y)))+
    inner ℂ (lowerL j (preRaiseR j x)) (T (inverse (inverse y)))+
    inner ℂ (lowerR j (preRaiseL j x)) (T (inverse (inverse y))))

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

def tensorPreimage2 (x y : Fock n) : JointFock n :=
  tensor (inverseWeight 1 x) (inverseWeight 3 y)+
    tensor (inverseWeight 3 x) (inverseWeight 1 y)+
    tensor (inverseWeight 3 x) (inverseWeight 3 y)+
    (2:ℂ) • tensor (inverseWeight 2 x) (inverseWeight 2 y)-
    (2:ℂ) • tensor (inverseWeight 2 x) (inverseWeight 3 y)-
    (2:ℂ) • tensor (inverseWeight 3 x) (inverseWeight 2 y)

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

def generatorPairingL (r : ℝ) (x y : I → JointFock n)
    (Z : JointFock n →L[ℂ] JointFock n) : ℂ :=
  ∑ j, (((r+1:ℝ):ℂ)*(∑' i, quadMinusL j (x i) (y i) Z)+
    (r:ℂ)*(∑' i, quadPlusL j (x i) (y i) Z))
def generatorPairingR (r : ℝ) (x y : I → JointFock n)
    (Z : JointFock n →L[ℂ] JointFock n) : ℂ :=
  ∑ j, (((r+1:ℝ):ℂ)*(∑' i, quadMinusR j (x i) (y i) Z)+
    (r:ℂ)*(∑' i, quadPlusR j (x i) (y i) Z))

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

def singleGeneratorPairing (r : ℝ) (x : I → Fock n) (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  ∑ j, (((r+1:ℝ):ℂ)*(CrossEnsemble.pairing
      (fun i => sandwich 0 3 (by omega) j (x i)) (fun i => sandwich 0 3 (by omega) j (x i)) Z-
    (2:ℂ)⁻¹*(CrossEnsemble.pairing (fun i => inverseWeight 2 (modeBound j false (x i))) (fun i => inverseWeight 3 (x i)) Z+
      CrossEnsemble.pairing (fun i => inverseWeight 3 (x i)) (fun i => inverseWeight 2 (modeBound j false (x i))) Z))+
    (r:ℂ)*(CrossEnsemble.pairing
      (fun i => creationSandwich 0 3 (by omega) j (x i)) (fun i => creationSandwich 0 3 (by omega) j (x i)) Z-
    (2:ℂ)⁻¹*(CrossEnsemble.pairing (fun i => inverseWeight 2 (modeBound j true (x i))) (fun i => inverseWeight 3 (x i)) Z+
      CrossEnsemble.pairing (fun i => inverseWeight 3 (x i)) (fun i => inverseWeight 2 (modeBound j true (x i))) Z)))

end BeamLadder

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end CrossEnsemble

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

def tensorRatio (ke : NumberIndex n × NumberIndex n) : ℝ :=
  W ke/(numberWeight ke.1*numberWeight ke.2)

def retainedRatio (ke : NumberIndex n × NumberIndex n) : ℝ := numberWeight ke.1/W ke

theorem tensorRatio_mem (ke : NumberIndex n × NumberIndex n) : tensorRatio ke ∈ Set.Icc 0 1 := by
  have h1 := numberWeight_one_le ke.1
  have h2 := numberWeight_one_le ke.2
  have hw : 0<W ke := by linarith [W_one_le ke]
  have hd : 0<numberWeight ke.1*numberWeight ke.2 := mul_pos (by linarith) (by linarith)
  refine ⟨div_nonneg hw.le hd.le, (div_le_one hd).mpr ?_⟩
  dsimp [W]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

theorem retainedRatio_mem (ke : NumberIndex n × NumberIndex n) : retainedRatio ke ∈ Set.Icc 0 1 := by
  have hw : 0<W ke := by linarith [W_one_le ke]
  refine ⟨div_nonneg (by linarith [numberWeight_one_le ke.1]) hw.le, (div_le_one hw).mpr ?_⟩
  dsimp [W]
  linarith [numberWeight_one_le ke.2]

theorem ratioSquare_norm {a : ℝ} (ha : a ∈ Set.Icc 0 1) : ‖(a^2:ℝ) • (1:ℂ)‖≤1 := by
  simp only [norm_smul, norm_one, mul_one, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
  nlinarith [ha.1,ha.2]

def tensorRatioCLM : JointFock n →L[ℂ] JointFock n :=
  WeightedShift.pullCLM id Function.injective_id (fun ke => ((tensorRatio ke)^2:ℂ))
    1 (by norm_num) (fun ke => by simpa only [Complex.real_smul,mul_one,Complex.ofReal_pow] using ratioSquare_norm (tensorRatio_mem ke))

def retainedRatioCLM : JointFock n →L[ℂ] JointFock n :=
  WeightedShift.pullCLM id Function.injective_id (fun ke => ((retainedRatio ke)^2:ℂ))
    1 (by norm_num) (fun ke => by simpa only [Complex.real_smul,mul_one,Complex.ofReal_pow] using ratioSquare_norm (retainedRatio_mem ke))

def weightedColumn (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : Fock n) : Fock n →L[ℂ] JointFock n :=
  retainedRatioCLM ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    tensorRatioCLM ∘L tensorRight y

@[simp] theorem weightedColumn_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (x y : Fock n) :
    weightedColumn η hη y x = retainedRatioCLM (beamUnitary η hη (tensorRatioCLM (tensor x y))) := rfl

end BeamLadder

namespace EnsemblePullback

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {I : Type*}

def compression (V : E →L[ℂ] F) (Z : F →L[ℂ] F) : E →L[ℂ] E :=
  V.adjoint ∘L Z ∘L V

def pullback (V : I → E →L[ℂ] F) (Z : F →L[ℂ] F) : E →L[ℂ] E :=
  ∑' i, compression (V i) Z

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {I J : Type*}

end EnsemblePullback

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

def weightedConditional (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : J → Fock n)
    (B : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  EnsemblePullback.pullback (fun j => weightedColumn η hη (y j)) (liftLeft B)

def weightedSlices (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : J → Fock n)
    (x : I → Fock n) (ije : (I × J) × NumberIndex n) : Fock n :=
  slice (weightedColumn η hη (y ije.1.2) (x ije.1.1)) ije.2

end BeamLadder

namespace CrossEnsemble
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {I : Type*}
end CrossEnsemble

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

end Annihilation

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I : Type*}

end BeamLadder

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I K : Type*}

def pushedDissipator (F : (I → Fock n) → K → Fock n) (x : I → Fock n)
    (j : Fin n) (upward : Bool) : Fock n →L[ℂ] Fock n :=
  CrossEnsemble.operator (F (fun i => gain j upward (x i))) (F (fun i => gain j upward (x i)))-
    (2:ℂ)⁻¹ • (CrossEnsemble.operator (F (fun i => modeBound j upward (x i))) (F (fun i => inverseWeight 1 (x i)))+
      CrossEnsemble.operator (F (fun i => inverseWeight 1 (x i))) (F (fun i => modeBound j upward (x i))))

def pushedGenerator (F : (I → Fock n) → K → Fock n) (r : ℝ) (x : I → Fock n) : Fock n →L[ℂ] Fock n :=
  ∑ j, (((r+1:ℝ):ℂ) • pushedDissipator F x j false+(r:ℂ) • pushedDissipator F x j true)

def pushedPairing (F : (I → Fock n) → K → Fock n) (r : ℝ) (x : I → Fock n)
    (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  ∑ j, (((r+1:ℝ):ℂ)*(CrossEnsemble.pairing (F (fun i => gain j false (x i))) (F (fun i => gain j false (x i))) Z-
      (2:ℂ)⁻¹*(CrossEnsemble.pairing (F (fun i => modeBound j false (x i))) (F (fun i => inverseWeight 1 (x i))) Z+
        CrossEnsemble.pairing (F (fun i => inverseWeight 1 (x i))) (F (fun i => modeBound j false (x i))) Z))+
    (r:ℂ)*(CrossEnsemble.pairing (F (fun i => gain j true (x i))) (F (fun i => gain j true (x i))) Z-
      (2:ℂ)⁻¹*(CrossEnsemble.pairing (F (fun i => modeBound j true (x i))) (F (fun i => inverseWeight 1 (x i))) Z+
        CrossEnsemble.pairing (F (fun i => inverseWeight 1 (x i))) (F (fun i => modeBound j true (x i))) Z)))

end WeightedGenerator

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

def weightedColumnRight (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : Fock n) : Fock n →L[ℂ] JointFock n :=
  retainedRatioCLM ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    tensorRatioCLM ∘L tensorLeft y

@[simp] theorem weightedColumnRight_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (x y : Fock n) :
    weightedColumnRight η hη y x = retainedRatioCLM (beamUnitary η hη (tensorRatioCLM (tensor y x))) := rfl

def weightedConditionalRight (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : J → Fock n)
    (B : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  EnsemblePullback.pullback (fun j => weightedColumnRight η hη (y j)) (liftLeft B)

def weightedSlicesRight (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : J → Fock n)
    (x : I → Fock n) (ije : (I × J) × NumberIndex n) : Fock n :=
  slice (weightedColumnRight η hη (y ije.1.2) (x ije.1.1)) ije.2

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end BeamLadder

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I : Type*}

end CrossEnsemble

end

end OAI


