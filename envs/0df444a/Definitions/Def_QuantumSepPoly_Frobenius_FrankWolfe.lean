-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_FrankWolfe
-- name    : QuantumSepPoly_Frobenius_FrankWolfe
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:26.01517+00:00
-- url     : https://prove2.me/theorems/b4b5c818-02a3-4369-a1af-d9b299e96643
-- title:
--   Adaptive amplified Frank-Wolfe execution and potential
-- statement:
--   Use $T=\lceil256/\eta^2\rceil$, $\tau=\eta^2/64$, and start from the first pure product density. At a nonzero residual, run the supplied finite program on $(\rho-\sigma_t)/\|\rho-\sigma_t\|_F$ with fresh supplied tapes, retain the best of the finitely many returned product vectors, and update
--   $$\sigma_{t+1}=(1-2/(t+2))\sigma_t+(2/(t+2))\omega_t.$$
--   The potential subtracts the actual minimum squared distance to Sep. Equality with the input freezes the process, representing early acceptance. The good-event predicate checks unit outputs and the required support approximation on the actual adaptive inputs. It asserts no independence or unproved correctness of those calls.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), §§2–5, p. 23 (PDF p. 23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_AlgorithmIO
import Definitions.Def_QuantumSepPoly_Frobenius_SeparableStates

noncomputable section

namespace QuantumSepPoly.Frobenius

/-- §5.3, pp.23–24: the potential is computed from the actual separable set. -/
def potential {d : ℕ} (ρ σ : Bip d) : ℝ :=
  (1/2 : ℝ) * (frob (σ-ρ))^2 -
    sInf ((fun ψ => (1/2 : ℝ) * (frob (ψ-ρ))^2) '' Sep d)

def fwIterations (η : ℝ) : ℕ := Nat.ceil (256 / η^2)
def fwAccuracy (η : ℝ) : ℝ := η^2 / 64

def fwInput {d : ℕ} (ρ σ : Bip d) : Bip d := (1 / (frob (ρ-σ) : ℂ)) • (ρ-σ)

def fwUpdate {d : ℕ} (t : ℕ) (σ ω : Bip d) : Bip d :=
  (1 - 2 / ((t : ℂ)+2)) • σ + (2 / ((t : ℂ)+2)) • ω

end QuantumSepPoly.Frobenius

namespace QuantumSepPoly.Frobenius

/-- Finite amplification by evaluation and comparison of actual program outputs. -/
noncomputable def bestProgramPair {d : ℕ} (P : RAMProgram) (τ : ℝ) (M : Bip d)
    (ell : ℕ) (tapes : ℕ → RandomTape) : Vec d × Vec d :=
  ((List.range ell).drop 1).foldl (fun best j =>
    let candidate := productOutput P τ M (tapes j)
    if productValue M candidate.1 candidate.2 > productValue M best.1 best.2 then candidate else best)
    (if ell = 0 then (firstVector d,firstVector d) else productOutput P τ M (tapes 0))

/-- The actual high-level adaptive process in §5.3; every call runs finite RAM code.
Zero residuals stop the source algorithm and are represented by a frozen state. -/
noncomputable def fwState {d : ℕ} (P : RAMProgram) (η : ℝ) (ρ : Bip d)
    (ell : ℕ) (tapes : ℕ → ℕ → RandomTape) : ℕ → Bip d
  | 0 => productDensity (firstVector d) (firstVector d)
  | t+1 => let σ := fwState P η ρ ell tapes t
      if σ = ρ then σ else
        let xy := bestProgramPair P (fwAccuracy η) (fwInput ρ σ) ell (tapes t)
        fwUpdate (t+1) σ (productDensity xy.1 xy.2)

noncomputable def fwGoodEvent {d : ℕ} (P : RAMProgram) (η : ℝ) (ρ : Bip d)
    (ell : ℕ) (tapes : ℕ → ℕ → RandomTape) : Prop :=
  ∀ t, t+1 < fwIterations η → let σ := fwState P η ρ ell tapes t
    σ ≠ ρ → let xy := bestProgramPair P (fwAccuracy η) (fwInput ρ σ) ell (tapes t)
      vecSq xy.1 = 1 ∧ vecSq xy.2 = 1 ∧
      productValue (fwInput ρ σ) xy.1 xy.2 ≥ support (fwInput ρ σ) - fwAccuracy η

end QuantumSepPoly.Frobenius


