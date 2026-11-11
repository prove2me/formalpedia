-- Prove2me | Definitions.Def_RandPurIso_Completion_contractionOracle
-- name    : RandPurIso_Completion_contractionOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:27:54.575882+00:00
-- url     : https://prove2.me/theorems/1171ea4e-86a9-4450-ab12-a37d77da36c0
-- title:
--   The oracle $\Phi^W$ of a stateful contraction
-- statement:
--   For a contraction $W:\mathsf{In}\otimes\mathsf{St}\to\mathsf{Out}\otimes\mathsf{St}$ and an initial state $|\varphi\rangle$ of $\mathsf{St}$, the oracle $\Phi^W$ maps
--   $$\rho\mapsto W\rho W^\dagger+\operatorname{Tr}\big((I-W^\dagger W)\rho\big)\,|\perp\rangle\langle\perp|_{\mathsf{Out}}\otimes|\varphi\rangle\langle\varphi|_{\mathsf{St}}$$
--   with output register $\mathsf{Out}_\perp\otimes\mathsf{St}$ and initial state $|\varphi\rangle$. With no private register ($\mathsf{St}$ trivial) this is exactly $\Phi_W$ of Definition 3.4; the paper's notation $A^V$ means $A^{\Phi_V}$.
--
--   **Formalization Note** Definition 3.4 adjoins $|\perp\rangle$ to the whole output space $\mathsf{Out}\otimes\mathsf{St}$. To keep the oracle's output of the form $\mathsf{Out}'\otimes\mathsf{St}$ (Definition 3.2), $|\perp\rangle$ is embedded isometrically as $|\perp\rangle\otimes|\varphi\rangle$ (on failure the private register is returned to its initial state). `liftUnit` and `unitInit` give the stateless case.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Definitions 3.2 and 3.4, pp. 17–18

import Mathlib
import Definitions.Def_RandPurIso_Completion_Oracle
open Matrix

namespace RandPurIso.Completion

/-- **The oracle `Φ^W` of a (stateful) contraction** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definitions 3.2 and 3.4,
pp. 17–18; used for stateful `W : In ⊗ St → Out ⊗ St` in Lemmas 3.5, 3.6 and Theorems 3.14, 3.17).

For `W : In ⊗ St → Out ⊗ St` and initial state `φ`, the oracle maps
`ρ ↦ WρW† + Tr((I − W†W)ρ) |⊥⟩⟨⊥| ⊗ |φ⟩⟨φ|`, with output register `Out⊥ ⊗ St`.

**Formalization Note.** Definition 3.4 adjoins `|⊥⟩` to the whole output space `Out ⊗ St`; to keep
the oracle's output of the form `Out' ⊗ St` (Definition 3.2), `|⊥⟩` is embedded isometrically as
`|⊥⟩_Out ⊗ |φ⟩_St` (the failure branch leaves the private register in its initial state). For
`St = Unit` (`liftUnit`, `unitInit`) this is exactly `Φ_V` of Definition 3.4. -/
noncomputable def contractionOracle {In Out St : Type} [Fintype In] [Fintype Out] [Fintype St]
    [DecidableEq In] [DecidableEq St]
    (K : Matrix (Out × St) (In × St) ℂ) (φ : St → ℂ) : Oracle In (Option Out) St where
  map ρ := fun p q => match p.1, q.1 with
    | some o, some o' => (K * ρ * Kᴴ) (o, p.2) (o', q.2)
    | none, none => ((1 - Kᴴ * K) * ρ).trace * (φ p.2 * star (φ q.2))
    | _, _ => 0
  init := φ

/-- A map `X → Y` viewed as a map `X ⊗ St → Y ⊗ St` with the trivial private register `St = Unit`. -/
def liftUnit {X Y : Type} (K : Matrix Y X ℂ) : Matrix (Y × Unit) (X × Unit) ℂ :=
  fun p q => K p.1 q.1

/-- The (unique, normalized) initial state of the trivial private register. -/
def unitInit : Unit → ℂ := fun _ => 1

end RandPurIso.Completion


