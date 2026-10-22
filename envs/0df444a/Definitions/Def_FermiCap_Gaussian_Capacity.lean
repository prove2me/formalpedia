-- Prove2me | Definitions.Def_FermiCap_Gaussian_Capacity
-- name    : FermiCap_Gaussian_Capacity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:42:07.309981+00:00
-- url     : https://prove2.me/theorems/c47c21d0-8853-4c24-a01c-7fef1dc8198d
-- title:
--   Finite output ensembles and Gaussian and one-shot capacities
-- statement:
--   A finite ensemble has nonnegative weights $p_a$ summing to one. For output states $\rho_a$, its Holevo quantity is
--   $$\chi= S\left(\sum_a p_a\rho_a\right)-\sum_a p_a S(\rho_a).$$
--   The one-shot capacity $C_1(\Phi)$ is the supremum over all finite ensembles of outputs of arbitrary input states. The Gaussian capacity $C_1^g(\Phi)$ takes the same supremum with all inputs Gaussian in Definition 1's sense.
--
--   This module also defines minimum output entropies over all, even Gaussian, and Gaussian inputs; the sorted-coefficient expressions of Eqs. (27) and (34); the displayed $2^n$-state signaling family of §IV.B; and the diagonal attenuation matrix $B$. These are the quantities compared by the milestones and Theorem 1.
--
--   **Formalization Note** The capacities use real suprema, the minima use real infima, and arbitrary ensemble sizes are represented by `Fin m`. Output-state conditions prevent invoking entropy on a non-state if the generic map is not a channel.
-- source:
--   Bravyi, Classical capacity of fermionic product channels, arXiv:quant-ph/0507282v1, p. 1, eqs. (1)–(2); p. 2, eqs. (5), (8); p. 6, §IV; p. 7, eqs. (27), (34)

import Mathlib
import Definitions.Def_FermiCap_Gaussian_States

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open ShadowTomography.QuantumLB (vnEntropy)

namespace FermiCap.Gaussian

/-- A finite normalized probability distribution. -/
def IsProb {m : ℕ} (p : Fin m → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- Holevo quantity of a finite output ensemble, Eq. (2), in bits. -/
def holevo {n m : ℕ} (p : Fin m → ℝ) (ρ : Fin m → Op n) : ℝ :=
  vnEntropy (∑ a, (p a : ℂ) • ρ a) - ∑ a, p a * vnEntropy (ρ a)

/-- One-shot Holevo capacity over all finite ensembles of outputs of input states. -/
def oneShotCap (n : ℕ) (Φ : Op n → Op n) : ℝ :=
  sSup {v : ℝ | ∃ (m : ℕ) (p : Fin m → ℝ) (σ : Fin m → Op n),
    IsProb p ∧ (∀ a, IsDensity (σ a)) ∧ (∀ a, IsDensity (Φ (σ a))) ∧
      v = holevo p (fun a => Φ (σ a))}

/-- Gaussian Holevo capacity over all finite ensembles of Gaussian input states. -/
def gaussCap (n : ℕ) (Φ : Op n → Op n) : ℝ :=
  sSup {v : ℝ | ∃ (m : ℕ) (p : Fin m → ℝ) (σ : Fin m → Op n),
    IsProb p ∧ (∀ a, IsGaussian (σ a)) ∧ (∀ a, IsDensity (Φ (σ a))) ∧
      v = holevo p (fun a => Φ (σ a))}

/-- Minimum output entropy (represented as an infimum), Eq. (8). -/
def minOutEntropy (n : ℕ) (Φ : Op n → Op n) : ℝ :=
  sInf {v : ℝ | ∃ ρ : Op n, IsDensity ρ ∧ IsDensity (Φ ρ) ∧ v = vnEntropy (Φ ρ)}

/-- Minimum output entropy over even Gaussian inputs, §IV.A. -/
def minOutEvenGaussian (n : ℕ) (Φ : Op n → Op n) : ℝ :=
  sInf {v : ℝ | ∃ ρ : Op n, IsEvenGaussian ρ ∧ IsDensity (Φ ρ) ∧ v = vnEntropy (Φ ρ)}

/-- Minimum output entropy over Gaussian inputs, §IV.B. -/
def minOutGaussian (n : ℕ) (Φ : Op n → Op n) : ℝ :=
  sInf {v : ℝ | ∃ ρ : Op n, IsGaussian ρ ∧ IsDensity (Φ ρ) ∧ v = vnEntropy (Φ ρ)}

/-- Right-hand side of (27), for the attenuations already in decreasing order. -/
def evenFormula (n : ℕ) (b : Fin (2 * n) → ℝ) : ℝ :=
  ∑ j : Fin n,
    binEnt ((1 + b ⟨2 * j.val, by omega⟩ * b ⟨2 * j.val + 1, by omega⟩) / 2)

/-- Right-hand side of (34), for the attenuations already in decreasing order. -/
def gaussFormula (n : ℕ) (h : 1 ≤ n) (b : Fin (2 * n) → ℝ) : ℝ :=
  binEnt ((1 + b ⟨0, by omega⟩) / 2) +
    ∑ j : Fin (n - 1),
      binEnt ((1 + b ⟨2 * j.val + 1, by omega⟩ *
        b ⟨2 * j.val + 2, by omega⟩) / 2)

/-- A state in the 2^n-state optimal signaling family of §IV.B, p. 8.
Each bit independently selects the sign of one commuting factor. -/
def optimalInput (n : ℕ) (h : 1 ≤ n) (s : Fin n → Bool) : Op n :=
  let first : Op n := (1 : Op n) +
    (if s ⟨0, by omega⟩ then (-1 : ℂ) else 1) • majorana n ⟨0, by omega⟩
  let rest : Op n :=
    ((List.finRange (n - 1)).map (fun j =>
      (1 : Op n) +
        (if s ⟨j.val + 1, by omega⟩ then (-1 : ℂ) else 1) •
          ((Complex.I : ℂ) •
            (majorana n ⟨2 * j.val + 1, by omega⟩ *
              majorana n ⟨2 * j.val + 2, by omega⟩)))).prod
  (((2 : ℂ) ^ n)⁻¹) • (first * rest)

/-- The attenuation matrix B = diag(b₁,...,b₂ₙ). -/
def attenuationDiagonal (n : ℕ) (b : Fin (2 * n) → ℝ) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ := Matrix.diagonal b

end FermiCap.Gaussian


