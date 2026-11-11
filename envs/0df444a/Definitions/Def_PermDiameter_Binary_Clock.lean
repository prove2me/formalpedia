-- Prove2me | Definitions.Def_PermDiameter_Binary_Clock
-- name    : PermDiameter_Binary_Clock
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:12:16.104032+00:00
-- url     : https://prove2.me/theorems/eb0f8621-5c14-44e0-8985-360309e7bfd0
-- title:
--   Step 3 of the reduction: the clock $C_q=\langle c_3\rangle$, $G_3$, $\Sigma_3$, $\Delta=\Sigma_3\cup\Sigma_3^{-1}$, $g_2$, $g_3$
-- statement:
--   Step 3 adds the cyclic group $C_q=\langle c_3\rangle$, $c_3=c^q$, of order $q=4m-3$ as a direct factor: $G_3=G_2\times C_q$. The clocked generators are
--   $$\Sigma_3=\{(a,c_3^i):a\in\Gamma,\ i\in\{0,1,2\}\}\cup\{(a,c_3^i):a\in\Gamma_\triangleright\cup\Gamma_\triangleleft,\ i\in\{0,1\}\}\cup\{(a,1):a\in\Gamma_\diamond\},$$
--   and the output generating set is $\Delta=\Sigma_3\cup\Sigma_3^{-1}$. The target is $g_3=(g_2,c_3^{2m-2})$, where $g_2=(g_1,1)\in G_2$ is the diagonal copy of $g_1$ (constant value $g_1$, trivial shift).
--
--   The clock forces short words for $g_3$ to consist of fillers together with one entry and its matching exit (Proposition 3.12), while the available clock values keep every element short in a positive instance (Proposition 3.11).
--
--   **Formalization Note.** $G_3$, $\Sigma_3$ and $\Delta$ are subsets of `Wreath (Perm Ω₁) (C_r) × Perm (Fin dc)`; $\Sigma_3^{-1}$ is `{p | p⁻¹ ∈ Σ₃}`. The exponent $2m-2$ is a natural-number subtraction with $m\ge3$, so it does not truncate.
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 20 (§3.3: G3, Σ3, Δ, g2, g3)

import Mathlib
import Definitions.Def_PermDiameter_Binary_Wreath
import Definitions.Def_PermDiameter_Binary_LengthGap
import Definitions.Def_PermDiameter_Binary_WreathConstruction

namespace PermDiameter.Binary

/-!
# Step 3 of the reduction: the clock (Lohrey–Thumm, §3.3, p. 20)

`G₃ = G₂ × C_q` with `C_q = ⟨c₃⟩`, inside `(Sym(Ω₁) ≀ C_r) × Sym(Ω_c)`.
-/

open Equiv

variable {d0 : ℕ} {Sig0 : Finset (Perm (Fin d0))} {g0 : Perm (Fin d0)} {k0 : ℕ}

namespace WreathData

variable {D : LengthGapData Sig0 g0 k0} (W : WreathData D)

/-- `G₃ = G₂ × C_q`, `C_q = ⟨c₃⟩`. -/
def G3 : Set (Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r) × Perm (Fin D.dc)) :=
  {p | p.1 ∈ W.G2 ∧ p.2 ∈ Subgroup.zpowers D.c3}

/-- The clocked generators
`Σ₃ = {(a, c₃ⁱ) : a ∈ Γ, i ∈ {0,1,2}} ∪ {(a, c₃ⁱ) : a ∈ Γ▷ ∪ Γ◁, i ∈ {0,1}} ∪ {(a, 1) : a ∈ Γ⋄}`. -/
def Sig3 : Set (Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r) × Perm (Fin D.dc)) :=
  {p | (p.1 ∈ W.Gamma ∧ ∃ i ∈ ({0, 1, 2} : Finset ℕ), p.2 = D.c3 ^ i) ∨
    ((W.IsEntry p.1 ∨ W.IsExit p.1) ∧ ∃ i ∈ ({0, 1} : Finset ℕ), p.2 = D.c3 ^ i) ∨
    (W.IsBridge p.1 ∧ p.2 = 1)}

/-- The output generating set `Δ = Σ₃ ∪ Σ₃⁻¹`. -/
def Delta : Set (Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r) × Perm (Fin D.dc)) :=
  W.Sig3 ∪ {p | p⁻¹ ∈ W.Sig3}

/-- `g₂ = (g₁, 1)`, the diagonal copy of `g₁` in `G₂` (constant value `g₁`, trivial shift). -/
def g2 : Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r) := ⟨fun _ => D.g1, 1⟩

/-- `g₃ = (g₂, c₃^{2m−2})`. -/
def g3 : Wreath (Perm (Omega1 d0 D.dc)) (Pos W.r) × Perm (Fin D.dc) :=
  (W.g2, D.c3 ^ (2 * D.m - 2))

end WreathData

end PermDiameter.Binary


