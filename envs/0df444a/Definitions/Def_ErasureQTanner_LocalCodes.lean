-- Prove2me | Definitions.Def_ErasureQTanner_LocalCodes
-- name    : ErasureQTanner_LocalCodes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:22.764202+00:00
-- url     : https://prove2.me/theorems/05115826-d4da-4240-ad2f-33c0d910c97e
-- title:
--   The four inner codes, the check bases and the requirements on them
-- statement:
--   A quantum Tanner code has four **inner codes** $C_A,C_B,D_A,D_B\subseteq\mathbb F_2^\Delta$. The check equations come from bases of four tensor codes: $C_A\otimes C_B$ on $V_{00}$, $D_A\otimes D_B$ on $V_{11}$, $C_A^\perp\otimes D_B^\perp$ on $V_{01}$ and $D_A^\perp\otimes C_B^\perp$ on $V_{10}$. This item bundles the codes with these bases.
--
--   The requirement `GoodLocal` $(\delta,\kappa)$ says that the four codes and their duals have minimum distance at least $\delta\Delta$, and that the pairs
--   $$(C_A,C_B),(C_A^\perp,C_B^\perp),(D_A,D_B),(D_A^\perp,D_B^\perp),(C_A,D_B),(C_A^\perp,D_B^\perp),(D_A,C_B),(D_A^\perp,C_B^\perp)$$
--   all have robustness $\kappa$.
--
--   **Formalization Note** Page 7 defines robustness of a pair on $(C_A^\perp\otimes C_B^\perp)^\perp$, and p.20 defines it for $(C_1\otimes C_2)^\perp$ with columns in $C_1^\perp$. Under these two conventions "the four tensor codes" name different pairs, and the sketch of §10.1 uses both, so all eight are required. Each is the published `QAlgorithms.IsProductExpanding X Y Δ κ`, columns in $X$, rows in $Y$. Random codes supply all eight.
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), §4, pp.6–7; §9, p.20; §10.1, p.25

import Mathlib
import Definitions.Def_QAlgorithms_Defs_TensorCode

set_option autoImplicit false

open QAlgorithms

namespace ErasureQTanner

/-- The four inner codes and the check bases: Pfister, Sprumont, Zémor, STOC 2027 submission (manuscript sha256
bf7a84a5…), §4, p.6: "On the local views of vertices of `V00` we put equations drawn from a basis of the tensor code
`C_A ⊗ C_B`, and for vertices of `V11` we put equations drawn from a basis of `D_A ⊗ D_B`. For vertices of `V01` we use the
code `C_A^⊥ ⊗ D_B^⊥` and for vertices of `V10` we use the code `D_A^⊥ ⊗ C_B^⊥`."

**Formalization Note.** Fixing the bases is what fixes the matrices `H_X`, `H_Z` and the syndromes the decoder reads. -/
structure LocalCodes (Δ : ℕ) where
  CA : Submodule (ZMod 2) (Fin Δ → ZMod 2)
  CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)
  DA : Submodule (ZMod 2) (Fin Δ → ZMod 2)
  DB : Submodule (ZMod 2) (Fin Δ → ZMod 2)
  r00 : ℕ
  r11 : ℕ
  r01 : ℕ
  r10 : ℕ
  b00 : Module.Basis (Fin r00) (ZMod 2) (tensorCode CA CB)
  b11 : Module.Basis (Fin r11) (ZMod 2) (tensorCode DA DB)
  b01 : Module.Basis (Fin r01) (ZMod 2) (tensorCode (codeDual CA) (codeDual DB))
  b10 : Module.Basis (Fin r10) (ZMod 2) (tensorCode (codeDual DA) (codeDual CB))

/-- The hypotheses on the inner codes (§4, p.7): "we need the component codes `C_A, C_B, D_A, D_B` and their duals to all
have good distance … all their minimum distances are at least `δ∆`", and "the four tensor codes on Figure 3 should have
sufficient robustness".

**Formalization Note.** p.7 defines robustness of a pair `(C_A, C_B)` on `(C_A^⊥ ⊗ C_B^⊥)^⊥`; p.20 defines it for the code
`(C₁ ⊗ C₂)^⊥` with `C₁^⊥`, `C₂^⊥` as columns and rows. Under these two conventions "the four tensor codes" name different
pairs, and the §10.1 sketch (p.25) uses both, for each of `C_X` and `C_Z`. So all eight pairs are required, each as
`QAlgorithms.IsProductExpanding X Y Δ κ` (columns in `X`, rows in `Y`). Theorem 12 and §4, p.7 supply all eight for random
codes. -/
def GoodLocal {Δ : ℕ} (δ κ : ℝ) (CA CB DA DB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) : Prop :=
  (∀ C ∈ [CA, CB, DA, DB, codeDual CA, codeDual CB, codeDual DA, codeDual DB],
      HasMinDistAtLeast C (δ * Δ)) ∧
  IsProductExpanding CA CB Δ κ ∧ IsProductExpanding (codeDual CA) (codeDual CB) Δ κ ∧
  IsProductExpanding DA DB Δ κ ∧ IsProductExpanding (codeDual DA) (codeDual DB) Δ κ ∧
  IsProductExpanding CA DB Δ κ ∧ IsProductExpanding (codeDual CA) (codeDual DB) Δ κ ∧
  IsProductExpanding DA CB Δ κ ∧ IsProductExpanding (codeDual DA) (codeDual CB) Δ κ

end ErasureQTanner


