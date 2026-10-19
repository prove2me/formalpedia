-- Prove2me | Definitions.Def_QAlgorithms_Defs_FiniteNoisyCircuits
-- name    : QAlgorithms_Defs_FiniteNoisyCircuits
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:37:20.783917+00:00
-- url     : https://prove2.me/theorems/0d70618f-262e-4559-977f-b1cbda926294
-- title:
--   FiniteNoisyCircuits
-- statement:
--   FiniteNoisyCircuits
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\FiniteNoisyCircuits.lean

import Definitions.Def_QAlgorithms_Defs_Channel
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.NoisyCircuits

/-- arxiv-1612.02058v3 PDF p.3; arxiv-1612.02058v3 PDF p.9. -/
structure ChannelBasis (n m : ℕ) where
  operation : Fin m → Superop (Qubits n) (Qubits n)
  channel : ∀ i, IsChannel (operation i)

/-- arxiv-1612.02058v3 PDF p.3; arxiv-1612.02058v3 PDF p.9. -/
def executeWord {I K : Type*} (operations : K → Superop I I) (word : List K) : Superop I I :=
  fun rho => word.foldl (fun X k => operations k X) rho

/-- A normalized Kraus operation preserves density matrices (1612.02058 p.9, Eq.(39)). -/
theorem channel_preserves_density {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (Phi : Superop I J) (hPhi : IsChannel Phi)
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) : IsDensityMatrix (Phi rho) := by
  obtain ⟨m,E,hE,hPhi⟩ := hPhi
  rw [hPhi]
  constructor
  · exact Matrix.posSemidef_sum Finset.univ (fun i _ => hrho.1.mul_mul_conjTranspose_same (E i))
  · have ht : ∀ i, (E i*rho*(E i)ᴴ).trace = ((E i)ᴴ*E i*rho).trace := by
      intro i; rw [Matrix.trace_mul_cycle]
    simp only [krausApply,Matrix.trace_sum,ht]
    rw [← Matrix.trace_sum,← Finset.sum_mul]
    change ((∑ i, (E i)ᴴ*E i)*rho).trace = 1
    rw [hE,one_mul,hrho.2]

/-- Chronological CPT execution preserves the initial density (1612.02058 p.3). -/
theorem word_preserves_density {n m : ℕ} (B : ChannelBasis n m) (word : List (Fin m))
    (rho : Matrix (Qubits n) (Qubits n) ℂ) (hrho : IsDensityMatrix rho) :
    IsDensityMatrix (executeWord B.operation word rho) := by
  induction word generalizing rho with
  | nil => exact hrho
  | cons i rest ih => exact ih _ (channel_preserves_density _ (B.channel i) _ hrho)

/-- Exact Born PMF of a mixed density matrix, without clipping (1612.02058 p.3). -/
def densityReadout {I : Type*} [Fintype I] [DecidableEq I]
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) : PMF I :=
  PMF.ofFintype (fun z => ENNReal.ofReal (rho z z).re) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => (hrho.1.diag_nonneg (i:=z)).1)]
    have ht : ∑ z, (rho z z).re = 1 := by
      simpa [Matrix.trace,Matrix.diag] using congrArg Complex.re hrho.2
    rw [ht]; simp)

/-- arxiv-1612.02058v3 PDF p.3. -/
def computationalReadoutLaw {n m : ℕ} (B : ChannelBasis n m) (word : List (Fin m)) : PMF (Qubits n) :=
  densityReadout (executeWord B.operation word (pureDensity (zeroKet n)))
    (word_preserves_density B word _ ⟨Matrix.posSemidef_vecMulVec_self_star _,by
      simp [pureDensity,zeroKet,ket,Matrix.trace,Matrix.diag]⟩)

/-- Sanity check for the source model (arxiv-1612.02058v3 PDF p.3). -/
example {I K : Type*} (operations : K → Superop I I) (rho : Matrix I I ℂ) :
    executeWord operations [] rho = rho := rfl

/-- Sanity check for the source model (arxiv-1612.02058v3 PDF p.3). -/
example {I K : Type*} (operations : K → Superop I I) (a b : K) (rho : Matrix I I ℂ) :
    executeWord operations [a,b] rho = operations b (operations a rho) := rfl

end QAlgorithms.NoisyCircuits


