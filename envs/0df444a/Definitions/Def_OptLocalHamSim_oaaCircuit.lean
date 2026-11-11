-- Prove2me | Definitions.Def_OptLocalHamSim_oaaCircuit
-- name    : OptLocalHamSim_oaaCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:43.924001+00:00
-- url     : https://prove2.me/theorems/6f0b8b06-3846-44b9-8e31-e8445e86e335
-- title:
--   Oblivious amplitude amplification: $\iota_{\mathrm{sig}}$, $\iota_0$, $R_{\mathrm{sig}}$ and $\mathcal U=-BR_{\mathrm{sig}}B^\dagger R_{\mathrm{sig}}B$
-- statement:
--   Let $W$, $S$, $D$ be the work, signal and data registers with zero states, the full space ordered $W\otimes S\otimes D$. Define
--
--   $$
--   \iota_{\mathrm{sig}}|\varphi\rangle_{SD}:=|0\rangle_W|\varphi\rangle_{SD},\qquad \iota_0|\psi\rangle:=\iota_{\mathrm{sig}}(|0\rangle_S|\psi\rangle_D),
--   $$
--
--   the zero-work subspace $\mathcal K:=\mathrm{ran}\,\iota_{\mathrm{sig}}$, and for an operator $B$ on the full space
--
--   $$
--   R_{\mathrm{sig}}:=I_W\otimes(2|0\rangle\langle0|_S-I_S)\otimes I_D,\qquad \mathcal U:=-BR_{\mathrm{sig}}B^\dagger R_{\mathrm{sig}}B .
--   $$
--
--   $B$ **preserves** $\mathcal K$ if it maps $\mathcal K$ into itself.
--
--   This is the one-step amplitude amplification that turns the block encoding $B$ of $\hat A_Q/2$ into a simulation circuit (Lemma 15).
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), §5.1, eqs. (86)–(87), pp.32–33

import Mathlib

open scoped Matrix

namespace OptLocalHamSim

variable {W S Dd : Type} [Fintype W] [DecidableEq W] [Fintype S] [DecidableEq S]
  [Fintype Dd] [DecidableEq Dd]

/-- `ι_sig|φ⟩_{SD} := |0⟩_W|φ⟩_{SD}`, eq. (86), p.32 (Shen, Wu, Yao, Yuan, Zhang, STOC 2027 submission,
held version, sha256 44a9768a…), for work, signal and data registers with basis sets `W`, `S`, `Dd`
and zero states `w0`, `s0`. The full space is ordered `W ⊗ S ⊗ D`. -/
def iotaSig (w0 : W) : Matrix (W × (S × Dd)) (S × Dd) ℂ :=
  Matrix.of fun x y => if x.1 = w0 ∧ x.2 = y then 1 else 0

/-- `ι₀|ψ⟩ := ι_sig(|0⟩_S|ψ⟩_D)`, eq. (86). -/
def iotaZero (w0 : W) (s0 : S) : Matrix (W × (S × Dd)) Dd ℂ :=
  Matrix.of fun x d => if x.1 = w0 ∧ x.2.1 = s0 ∧ x.2.2 = d then 1 else 0

/-- `B` **preserves** the zero-work subspace `K := ran ι_sig` (p.32). -/
def PreservesK (w0 : W) (B : Matrix (W × (S × Dd)) (W × (S × Dd)) ℂ) : Prop :=
  ∀ v : S × Dd → ℂ, B *ᵥ (iotaSig (Dd := Dd) w0 *ᵥ v) ∈
    LinearMap.range (Matrix.mulVecLin (iotaSig (S := S) (Dd := Dd) w0))

/-- The signal reflection `R_sig := I_W ⊗ (2|0⟩⟨0|_S − I_S) ⊗ I_D`, eq. (87), p.33. -/
def Rsig (s0 : S) : Matrix (W × (S × Dd)) (W × (S × Dd)) ℂ :=
  Matrix.of fun x y => if x = y then (if x.2.1 = s0 then 1 else -1) else 0

/-- The amplified circuit `𝒰 := −B R_sig B† R_sig B`, eq. (87). -/
def oaaCircuit (s0 : S) (B : Matrix (W × (S × Dd)) (W × (S × Dd)) ℂ) :
    Matrix (W × (S × Dd)) (W × (S × Dd)) ℂ :=
  -(B * Rsig s0 * Bᴴ * Rsig s0 * B)

end OptLocalHamSim


