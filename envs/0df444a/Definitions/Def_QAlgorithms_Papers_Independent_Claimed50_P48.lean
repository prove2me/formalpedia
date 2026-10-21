-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
-- name    : QAlgorithms_Papers_Independent_Claimed50_P48
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T11:36:31.08515+00:00
-- url     : https://prove2.me/theorems/6b927169-addd-4aab-bdde-e38c98131580
-- title:
--   Definitions for On complementary channels and the additivity problem
-- statement:
--   The objects the formalized statements of *On complementary channels and the additivity problem* (arXiv:quant-ph/0509101) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `FiniteKrausCP`: PDF pp.1,4: unnormalized finite Kraus form, extending frozen IsChannel.
--   - `CPComplementary`: PDF p.1, (1): two marginals of the SAME arbitrary linear V.
--   - `PartialIsometry`: PDF pp.2,10: rectangular partial isometry, including zero.
--   - `Equivalent`: PDF p.2, (2): both output conjugation identities on all operators.
--   - `MinimalDilation`: PDF p.2: minimum environment dimension among all finite dilations. No empty real infimum and no positivity assumption on the environment.
--   - `superopTensor`: PDF pp.3–4: matrix-unit tensor extension to ALL joint inputs. The accepted tensorMap uses bundled linear maps; the present maps are unbundled, with linearity supplied by their Kraus representations.
--   - `tensorDilation`: PDF p.4: regroup (B,C),(B2,C2) into (B,B2),(C,C2).
--   - `ValidExponent`: PDF p.2: finite p>=1 and the separate infinity endpoint.
--   - `nu`: PDF p.2, (3): the density set is nonempty and compact on nonzero finite input, and CP maps have bounded image. Infinity uses the accepted operator norm.
--   - `hmin`: PDF p.2: minimum output entropy, for a channel on nonzero finite input.
--   - `hhat`: PDF p.2: ALL finite normalized pure ensembles with computed barycenter rho. Attainment of this convexRoof infimum is asserted below.
--   - `Multiplicative`: PDF p.3, (4).
--   - `Additive`: PDF p.3, (5).
--   - `SuperadditiveAt`: PDF p.3, (6): rho's marginals are computed, never independently supplied.
--   - `Superadditive`: PDF p.3: the all-states property.
--   - `UniversalMultiplicative`: PDF p.3: EVERY finite CP partner; its output may have dimension zero.
--   - `UniversalAdditive`: PDF p.3: entropy partners are channels.
--   - `UniversalSuperadditive`: PDF p.3: every partner channel and every joint density.
--   - `nonzeroSpectrum`: PDF p.3: eigenvalues with multiplicity, deleting only zero eigenvalues.
--   - `indexedKrausDilation`: PDF p.4, (10)–(11): arbitrary finite index set version of the accepted Fin-indexed stinespringOperator. Output factor precedes environment.
--   - `rowKraus`: PDF p.4, (12): complementary Kraus operators are output rows.
--   - `rankOneKraus`: PDF p.4, (13): the vectors need not be normalized or orthogonal.
--   - `HasRankOneKraus`: PDF p.4: rank-one Kraus characterization, for rectangular CP maps.
--   - `gram`: PDF pp.4–5, (14): the source bra order is <phi_beta|phi_alpha>.
--   - `arbitraryVectorComplement`: PDF pp.4–5, (14): arbitrary psi, without a basis assumption.
--   - `gramKraus`: PDF p.5, (15): c_ab=sum_j v_aj conjugate(v_bj).
--   - `IsDiagonal`: PDF p.5: diagonal in a COMMON orthonormal input/output basis.
--   - `DiagonalEquivalent`: PDF pp.1,5: the same diagonal class compared up to output equivalence (2).
--   - `EBComplement`: PDF pp.1,4–5: exact complements of EB CP maps.
--   - `basisColumns`: PDF p.5: column vectors of an orthonormal basis change.
--   - `CommutingNormal`: PDF p.5: both normality and every pairwise commutator are required.
--   - `ProjectiveAction`: PDF p.6: projective unitary actions with their multipliers retained.
--   - `AllOperatorCovariant`: PDF p.6, (16): all group elements and all operators.
--   - `antisymmetricKraus`: PDF p.7, (17): d^2 ordered-pair Kraus indices, including zero diagonals.
--   - `antisymmetricComplement`: PDF p.8, (18): computed complement with all d^2 output coordinates.
--   - `antisymmetricRows`: PDF p.8: d complementary Kraus maps into d^2 dimensions.
--   - `depolarizingS`: PDF p.8: S with NORMALIZED Omega; formula checked in the rendered PDF.
--   - `depolarizingComplement`: PDF pp.8–9: computed S(rho tensor I)S on the whole CP interval.
--   - `dilationReshuffle`: PDF p.9: dilationReshuffle computed from V, S_(c,(a,b))=V_((b,c),a).
--   - `operatorTraceDual`: PDF pp.10–11: computed linear trace-dual. For CP maps it equals the Hilbert–Schmidt adjoint; no independently supplied dual is assumed.
--   - `attenuationBogoliubov`: PDF pp.9–10: amplitude k, with the literal minus sign in the second annihilator. These are finite COEFFICIENTS, not bounded ladder operators.
--   - `amplificationBogoliubov`: PDF p.10: both plus signs are literal; the second marginal is phase conjugating. Full operational realization is deferred, not assumed.
-- source:
--   On complementary channels and the additivity problem, arXiv:quant-ph/0509101v3, https://arxiv.org/abs/quant-ph/0509101v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

/-! Holevo, arXiv:quant-ph/0509101v3. All pages are PDF pages.
CP maps need not preserve trace. Entropies use natural logarithms.
All new definitions are paper-local. Four deferred nodes are in HARD.md.
Compilation is pending the mechanical batch handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)
open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)
open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)
open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]
variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

/-- PDF pp.1,4: unnormalized finite Kraus form, extending frozen IsChannel. -/
def FiniteKrausCP (Phi : Superop A B) : Prop :=
  ∃ r : ℕ, ∃ E : Fin r → Matrix B A ℂ, Phi = krausApply E

/-- PDF p.1, (1): two marginals of the SAME arbitrary linear V. -/
def CPComplementary (Phi : Superop A B) (Psi : Superop A C) : Prop :=
  ∃ V : Matrix (B × C) A ℂ, receiverChannel V = Phi ∧ complementaryChannel V = Psi

/-- PDF pp.2,10: rectangular partial isometry, including zero. -/
def PartialIsometry (W : Matrix C B ℂ) : Prop := W * Wᴴ * W = W

/-- PDF p.2, (2): both output conjugation identities on all operators. -/
def Equivalent (Phi : Superop A B) (Psi : Superop A C) : Prop :=
  ∃ W : Matrix C B ℂ, PartialIsometry W ∧
    (∀ rho, Psi rho = W * Phi rho * Wᴴ) ∧ (∀ rho, Phi rho = Wᴴ * Psi rho * W)

/-- PDF p.2: minimum environment dimension among all finite dilations.
No empty real infimum and no positivity assumption on the environment. -/
def MinimalDilation (Phi : Superop A B) (V : Matrix (B × C) A ℂ) : Prop :=
  receiverChannel V = Phi ∧ ∀ (r : ℕ) (W : Matrix (B × Fin r) A ℂ),
    receiverChannel W = Phi → Fintype.card C ≤ r

/-- PDF pp.3–4: matrix-unit tensor extension to ALL joint inputs.
The accepted tensorMap uses bundled linear maps; the present maps are unbundled,
with linearity supplied by their Kraus representations. -/
def superopTensor (Phi : Superop A B) (Psi : Superop A2 B2) : Superop (A × A2) (B × B2) :=
  fun X => ∑ a, ∑ b, ∑ c, ∑ d,
    X (a,b) (c,d) • ((Phi (Matrix.single a c 1)) ⊗ₖ (Psi (Matrix.single b d 1)))

/-- PDF p.4: regroup (B,C),(B2,C2) into (B,B2),(C,C2). -/
def tensorDilation (V : Matrix (B × C) A ℂ) (W : Matrix (B2 × C2) A2 ℂ) :
    Matrix ((B × B2) × (C × C2)) (A × A2) ℂ :=
  fun bc a => V (bc.1.1,bc.2.1) a.1 * W (bc.1.2,bc.2.2) a.2

/-- PDF p.2: finite p>=1 and the separate infinity endpoint. -/
def ValidExponent (p : ℝ≥0∞) : Prop := 1 ≤ p

/-- PDF p.2, (3): the density set is nonempty and compact on nonzero finite
input, and CP maps have bounded image. Infinity uses the accepted operator norm. -/
def nu (p : ℝ≥0∞) (Phi : Superop A B) : ℝ :=
  sSup {x | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧ x = schattenNorm p (Phi rho)}

/-- PDF p.2: minimum output entropy, for a channel on nonzero finite input. -/
def hmin (Phi : Superop A B) : ℝ :=
  sInf {x | ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧ x = entropy (Phi rho)}

/-- PDF p.2: ALL finite normalized pure ensembles with computed barycenter
rho. Attainment of this convexRoof infimum is asserted below. -/
def hhat (Phi : Superop A B) (rho : Matrix A A ℂ) : ℝ :=
  convexRoof (fun psi => entropy (Phi (pureDensity psi))) rho

/-- PDF p.3, (4). -/
def Multiplicative (p : ℝ≥0∞) (Phi : Superop A B) (Psi : Superop A2 B2) : Prop :=
  nu p (superopTensor Phi Psi) = nu p Phi * nu p Psi

/-- PDF p.3, (5). -/
def Additive (Phi : Superop A B) (Psi : Superop A2 B2) : Prop :=
  hmin (superopTensor Phi Psi) = hmin Phi + hmin Psi

/-- PDF p.3, (6): rho's marginals are computed, never independently supplied. -/
def SuperadditiveAt (Phi : Superop A B) (Psi : Superop A2 B2)
    (rho : Matrix (A × A2) (A × A2) ℂ) : Prop :=
  hhat Phi (traceRight rho) + hhat Psi (traceLeft rho) ≤ hhat (superopTensor Phi Psi) rho

/-- PDF p.3: the all-states property. -/
def Superadditive (Phi : Superop A B) (Psi : Superop A2 B2) : Prop :=
  ∀ rho, IsDensityMatrix rho → SuperadditiveAt Phi Psi rho

/-- PDF p.3: EVERY finite CP partner; its output may have dimension zero. -/
def UniversalMultiplicative (p : ℝ≥0∞) (Phi : Superop A B) : Prop :=
  ∀ (n m : ℕ), 0 < n → ∀ Psi : Superop (Fin n) (Fin m),
    FiniteKrausCP Psi → Multiplicative p Phi Psi

/-- PDF p.3: entropy partners are channels. -/
def UniversalAdditive (Phi : Superop A B) : Prop :=
  ∀ (n m : ℕ), 0 < n → ∀ Psi : Superop (Fin n) (Fin m),
    IsChannel Psi → Additive Phi Psi

/-- PDF p.3: every partner channel and every joint density. -/
def UniversalSuperadditive (Phi : Superop A B) : Prop :=
  ∀ (n m : ℕ), 0 < n → ∀ Psi : Superop (Fin n) (Fin m),
    IsChannel Psi → Superadditive Phi Psi

/-- PDF p.3: eigenvalues with multiplicity, deleting only zero eigenvalues. -/
def nonzeroSpectrum (X : Matrix A A ℂ) : Multiset ℝ :=
  ((Finset.univ : Finset (Fin (Fintype.card A))).val.map (ascEigenvalues X)).filter (fun x => x ≠ 0)

/-- PDF p.4, (10)–(11): arbitrary finite index set version of the accepted
Fin-indexed stinespringOperator. Output factor precedes environment. -/
def indexedKrausDilation (E : K → Matrix B A ℂ) : Matrix (B × K) A ℂ := fun bk a => E bk.2 bk.1 a

/-- PDF p.4, (12): complementary Kraus operators are output rows. -/
def rowKraus (E : K → Matrix B A ℂ) : B → Matrix K A ℂ := fun b k a => E k b a

/-- PDF p.4, (13): the vectors need not be normalized or orthogonal. -/
def rankOneKraus (psi : K → EuclideanSpace ℂ A) (phi : K → EuclideanSpace ℂ B) :
    K → Matrix B A ℂ := fun k b a => phi k b * conj (psi k a)

/-- PDF p.4: rank-one Kraus characterization, for rectangular CP maps. -/
def HasRankOneKraus (Phi : Superop A B) : Prop :=
  ∃ r : ℕ, ∃ psi : Fin r → EuclideanSpace ℂ A,
    ∃ phi : Fin r → EuclideanSpace ℂ B, Phi = krausApply (rankOneKraus psi phi)

/-- PDF pp.4–5, (14): the source bra order is <phi_beta|phi_alpha>. -/
def gram (phi : K → EuclideanSpace ℂ B) : Matrix K K ℂ := fun a b => inner ℂ (phi b) (phi a)

/-- PDF pp.4–5, (14): arbitrary psi, without a basis assumption. -/
def arbitraryVectorComplement (c : Matrix K K ℂ) (psi : K → EuclideanSpace ℂ A) : Superop A K :=
  fun rho a b => c a b * (∑ i, ∑ j, conj (psi a i) * rho i j * psi b j)

/-- PDF p.5, (15): c_ab=sum_j v_aj conjugate(v_bj). -/
def gramKraus (v : Matrix K B ℂ) (psi : K → EuclideanSpace ℂ A) : B → Matrix K A ℂ :=
  fun j a i => v a j * conj (psi a i)

/-- PDF p.5: diagonal in a COMMON orthonormal input/output basis. -/
def IsDiagonal (Phi : Superop A A) : Prop :=
  ∃ c : Matrix A A ℂ, c.PosSemidef ∧ ∃ U : Matrix.unitaryGroup A ℂ,
    ∀ rho, Phi rho = (U : Matrix A A ℂ) *
      Matrix.hadamard c ((U : Matrix A A ℂ)ᴴ * rho * (U : Matrix A A ℂ)) * (U : Matrix A A ℂ)ᴴ

/-- PDF pp.1,5: the same diagonal class compared up to output equivalence (2). -/
def DiagonalEquivalent (Phi : Superop A B) : Prop :=
  ∃ D : Superop A A, IsDiagonal D ∧ Equivalent D Phi

/-- PDF pp.1,4–5: exact complements of EB CP maps. -/
def EBComplement (Phi : Superop A B) : Prop :=
  ∃ n : ℕ, ∃ E : Superop A (Fin n), HasRankOneKraus E ∧ CPComplementary E Phi

/-- PDF p.5: column vectors of an orthonormal basis change. -/
def basisColumns (U : Matrix.unitaryGroup A ℂ) : A → EuclideanSpace ℂ A :=
  fun a => WithLp.toLp 2 (fun i => (U : Matrix A A ℂ) i a)

/-- PDF p.5: both normality and every pairwise commutator are required. -/
def CommutingNormal (E : K → Matrix A A ℂ) : Prop :=
  (∀ j, (E j)ᴴ * E j = E j * (E j)ᴴ) ∧ ∀ j k, E j * E k = E k * E j

/-- PDF p.6: projective unitary actions with their multipliers retained. -/
structure ProjectiveAction (G I : Type*) [Group G] [Fintype I] [DecidableEq I] where
  unitary : G → Matrix.unitaryGroup I ℂ
  multiplier : G → G → ℂ
  modulus : ∀ g h, ‖multiplier g h‖ = 1
  multiply : ∀ g h, (unitary (g * h) : Matrix I I ℂ) =
    multiplier g h • ((unitary g : Matrix I I ℂ) * (unitary h : Matrix I I ℂ))

/-- PDF p.6, (16): all group elements and all operators. -/
def AllOperatorCovariant {G : Type*} [Group G] (Phi : Superop A B)
    (UA : ProjectiveAction G A) (UB : ProjectiveAction G B) : Prop :=
  ∀ g rho, Phi ((UA.unitary g : Matrix A A ℂ) * rho * (UA.unitary g : Matrix A A ℂ)ᴴ) =
    (UB.unitary g : Matrix B B ℂ) * Phi rho * (UB.unitary g : Matrix B B ℂ)ᴴ

/-- PDF p.7, (17): d^2 ordered-pair Kraus indices, including zero diagonals. -/
def antisymmetricKraus (d : ℕ) : (Fin d × Fin d) → Matrix (Fin d) (Fin d) ℂ :=
  fun jk => ((Real.sqrt (2 * ((d : ℝ) - 1)))⁻¹ : ℂ) •
    (Matrix.single jk.1 jk.2 1 - Matrix.single jk.2 jk.1 1)

/-- PDF p.8, (18): computed complement with all d^2 output coordinates. -/
def antisymmetricComplement (d : ℕ) : Superop (Fin d) (Fin d × Fin d) :=
  fun rho => ((2 * ((d : ℂ) - 1))⁻¹) •
    ((1 - (environmentSwap (E := Fin d))) * (rho ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * (1 - (environmentSwap (E := Fin d))))

/-- PDF p.8: d complementary Kraus maps into d^2 dimensions. -/
def antisymmetricRows (d : ℕ) : Fin d → Matrix (Fin d × Fin d) (Fin d) ℂ :=
  fun j p i => ((Real.sqrt (2 * ((d : ℝ) - 1)))⁻¹ : ℂ) *
    ((if p.1 = i ∧ p.2 = j then 1 else 0) - (if p.1 = j ∧ p.2 = i then 1 else 0))

/-- PDF p.8: S with NORMALIZED Omega; formula checked in the rendered PDF. -/
def depolarizingS (d : ℕ) (hd : 0 < d) (t : ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  (Real.sqrt (t / d) : ℂ) • 1 +
    (Real.sqrt d * (-(Real.sqrt t) / d + Real.sqrt (1 - t * ((d : ℝ)^2 - 1) / (d : ℝ)^2)) : ℂ) •
      pureDensity (finiteMaxEntangled (Fin d))

/-- PDF pp.8–9: computed S(rho tensor I)S on the whole CP interval. -/
def depolarizingComplement (d : ℕ) (hd : 0 < d) (t : ℝ) : Superop (Fin d) (Fin d × Fin d) :=
  fun rho => depolarizingS d hd t * (rho ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * depolarizingS d hd t

/-- PDF p.9: dilationReshuffle computed from V, S_(c,(a,b))=V_((b,c),a). -/
def dilationReshuffle (V : Matrix (B × C) A ℂ) : Matrix C (A × B) ℂ := fun c ab => V (ab.2,c) ab.1

/-- PDF pp.10–11: computed linear trace-dual. For CP maps it equals the
Hilbert–Schmidt adjoint; no independently supplied dual is assumed. -/
def operatorTraceDual (Phi : Superop A B) (X : Matrix B B ℂ) : Matrix A A ℂ :=
  fun a b => (Phi (Matrix.single b a 1) * X).trace

/-- PDF pp.9–10: amplitude k, with the literal minus sign in the second
annihilator. These are finite COEFFICIENTS, not bounded ladder operators. -/
def attenuationBogoliubov (k : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let s : ℂ := (Real.sqrt (1 - k^2) : ℂ)
  ![![(k : ℂ),0,s,0], ![0,(k : ℂ),0,s], ![s,0,-(k : ℂ),0], ![0,s,0,-(k : ℂ)]]

/-- PDF p.10: both plus signs are literal; the second marginal is phase
conjugating. Full operational realization is deferred, not assumed. -/
def amplificationBogoliubov (k : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let s : ℂ := (Real.sqrt (k^2 - 1) : ℂ)
  ![![(k : ℂ),0,0,s], ![0,(k : ℂ),s,0], ![0,s,(k : ℂ),0], ![s,0,0,(k : ℂ)]]

/-! Sanity examples for local definitions. -/

example : ValidExponent ⊤ := by simp [ValidExponent]

example : PartialIsometry (0 : Matrix C B ℂ) := by simp [PartialIsometry]

example : PartialIsometry (1 : Matrix A A ℂ) := by simp [PartialIsometry]

example : FiniteKrausCP (fun _ : Matrix A A ℂ => (0 : Matrix B B ℂ)) := by
  refine ⟨0, fun i => Fin.elim0 i, ?_⟩
  funext rho
  simp [krausApply]

example (V : Matrix (B × C) A ℂ) :
    CPComplementary (receiverChannel V) (complementaryChannel V) := ⟨V,rfl,rfl⟩

example (Phi : Superop A B) : Equivalent Phi Phi := by
  refine ⟨1, by simp [PartialIsometry], ?_, ?_⟩ <;> intro rho <;> simp

example (Phi : Superop A B) : superopTensor Phi (fun _ : Matrix A2 A2 ℂ => (0 : Matrix B2 B2 ℂ)) =
    (fun _ => 0) := by funext X; simp [superopTensor]

example : entropy (0 : Matrix A A ℂ) = 0 := by simp [entropy]

example (E : K → Matrix B A ℂ) (b : B) (k : K) (a : A) :
    rowKraus E b k a = indexedKrausDilation E (b,k) a := rfl

example (psi : K → EuclideanSpace ℂ A) : arbitraryVectorComplement (0 : Matrix K K ℂ) psi =
    (fun _ => 0) := by funext rho a b; simp [arbitraryVectorComplement]

example (psi : K → EuclideanSpace ℂ A) : gramKraus (0 : Matrix K B ℂ) psi =
    (fun _ => 0) := by funext j a i; simp [gramKraus]

example (rho : Matrix A A ℂ) : Matrix.hadamard (1 : Matrix A A ℂ) rho = Matrix.diagonal (fun i => rho i i) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.hadamard, Matrix.one_apply, Matrix.diagonal_apply, h]

example : CommutingNormal (fun _ : K => (0 : Matrix A A ℂ)) := by simp [CommutingNormal]

example (V : Matrix (B × C) A ℂ) (c : C) (a : A) (b : B) :
    dilationReshuffle V c (a,b) = V (b,c) a := rfl

example (d : ℕ) (j : Fin d) : antisymmetricKraus d (j,j) = 0 := by simp [antisymmetricKraus]

example (i j : A) : (environmentSwap (E := A)) (i,j) (j,i) = 1 := by simp [environmentSwap]

example : attenuationBogoliubov 0 =
    (![![0,0,1,0], ![0,0,0,1], ![1,0,0,0], ![0,1,0,0]] : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [attenuationBogoliubov]

example : amplificationBogoliubov 1 = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [amplificationBogoliubov, Matrix.one_apply]

end QAlgorithms.Papers.Independent.Claimed50.P48


