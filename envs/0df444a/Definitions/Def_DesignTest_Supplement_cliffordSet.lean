-- Prove2me | Definitions.Def_DesignTest_Supplement_cliffordSet
-- name    : DesignTest_Supplement_cliffordSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:07:36.246549+00:00
-- url     : https://prove2.me/theorems/47f454e4-337f-43ac-972e-c7c874fa0e0b
-- title:
--   Finite-field Weyl operators and the restricted Clifford set $\mathcal C_d$ up to phase
-- statement:
--   Let $F$ be a finite field with $|F|=d$ labelling the basis of $\mathbb C^d$, and $\chi$ a nontrivial additive character of $F$. The **finite-field Weyl operators** are $W_{(x,z)}=Z(z)X(x)$ with $X(x)|y\rangle=|y+x\rangle$ and $Z(z)|y\rangle=\chi(zy)|y\rangle$. The **restricted Clifford set** is
--
--   $$\mathcal C_d=\{C_SW_a: S\in\mathrm{SL}(2,F),\ a\in F^2\},\qquad C_SW_aC_S^\dagger=\xi_{S,a}W_{Sa},\ |\xi_{S,a}|=1 .$$
--
--   Up to phase, a unitary $V$ lies in $\mathcal C_d$ exactly when, for some $S\in\mathrm{SL}(2,F)$, $VW_wV^\dagger$ is a scalar multiple of $W_{Sw}$ for every label $w$. The paper's list of $d^3(d^2-1)$ matrices is one phase representative per element; $\mu_C$ is uniform on it.
--
--   **Formalization Note.** The set is characterized intrinsically, closed under phases, and independent of the nontrivial character.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), §5.3, p.60, eq. (101)

import Mathlib
import Definitions.Def_DesignTest_Supplement_twirlDist

set_option autoImplicit false

namespace DesignTest.Supplement

open RandomGateDesign.MasterBound
open scoped Matrix

/-- **Finite-field Weyl operators** `W_{(x,z)} = Z(z) X(x)` on `ℂ^d`, the basis labelled by a finite field
`F` with `|F| = d` through `e : Fin d ≃ F`: `X(x)|y⟩ = |y + x⟩`, `Z(z)|y⟩ = χ(z y)|y⟩` for a nontrivial
additive character `χ` of `F` (A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*,
STOC 2027 submission (sha256 e2f0a429…), §5.3, p.60: "`{W_a : a ∈ F_d²}` be the finite-field Weyl
operators").

**Formalization Note.** Entry `(i, j)` is `χ(z · e i)` if `e i = e j + x`, else `0`. -/
def ffWeyl {F : Type} [Field F] [DecidableEq F] {d : ℕ} (e : Fin d ≃ F) (χ : AddChar F ℂ)
    (w : Fin 2 → F) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => if e i = e j + w 0 then χ (w 1 * e i) else 0

/-- **The restricted Clifford set `C_d` up to phase** (STOC 2027 submission (sha256 e2f0a429…), §5.3,
p.60): `C_d := {C_S W_a : S ∈ SL(2, F_d), a ∈ F_d²}`, where `C_S` is a Clifford operator with
`C_S W_a C_S† = ξ_{S,a} W_{Sa}`, `|ξ_{S,a}| = 1`.

**Formalization Note.** Characterized intrinsically: a unitary `V` lies in the set iff for some
`S ∈ SL(2, F)` and every label `w`, `V W_w V† = c W_{S w}` for a scalar `c`. Every `C_S W_a` satisfies
this (Weyl displacements change only conjugation phases), and conversely `C_S† V` then commutes with
every Weyl operator up to scalars, so `V ∝ C_S W_a` by irreducibility of the Weyl group. The set is
closed under global phases; the paper's list `C_d` of `d³(d² − 1)` matrices is a choice of one phase
representative per element (`IsPhaseReps`). The set does not depend on the nontrivial character `χ`
(a different one rescales `z`, which conjugates `SL(2, F)` into itself). -/
def cliffordUpToPhase {F : Type} [Field F] [DecidableEq F] {d : ℕ} (e : Fin d ≃ F)
    (χ : AddChar F ℂ) : Set (U d) :=
  {V | ∃ S : Matrix.SpecialLinearGroup (Fin 2) F, ∀ w : Fin 2 → F, ∃ c : ℂ,
    (V : Matrix (Fin d) (Fin d) ℂ) * ffWeyl e χ w * (V : Matrix (Fin d) (Fin d) ℂ)ᴴ =
      c • ffWeyl e χ ((S : Matrix (Fin 2) (Fin 2) F).mulVec w)}

end DesignTest.Supplement


