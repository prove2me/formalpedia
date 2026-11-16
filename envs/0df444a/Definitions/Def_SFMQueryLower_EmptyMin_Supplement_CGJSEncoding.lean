-- Prove2me | Definitions.Def_SFMQueryLower_EmptyMin_Supplement_CGJSEncoding
-- name    : SFMQueryLower_EmptyMin_Supplement_CGJSEncoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:27:11.945713+00:00
-- url     : https://prove2.me/theorems/6abef638-e39e-422e-bd7b-e41e2ac574fb
-- title:
--   Translating between CGJS functions and $\mathrm{HiddenPermutation}$ instances (Lemma C.5 and Definition C.7)
-- statement:
--   This file defines the two translations used in Appendix C.
--
--   1. **From a CGJS function to a hidden-permutation instance (Lemma C.5).** For $n=2k$ and a permutation $\pi$ of $[n]$, the string $z\in\{0,1\}^n$ has $z_{p_i^\pi}=1$ and $z_{r_i^\pi}=0$ for every $i\in[k]$ (so $z$ is the indicator of $P^\pi$), and the permutation $\sigma$ of $[n]$ is
--   $$\sigma(2(k-i)+1):=p_i^\pi,\qquad \sigma(2(k-i)+2):=r_i^\pi\qquad(i\in[k]),$$
--   which lists $p_k^\pi,r_k^\pi,p_{k-1}^\pi,r_{k-1}^\pi,\dots$.
--   2. **From a hidden-permutation instance to a CGJS function (Definition C.7).** For $k\ge2$, $z\in\{0,1\}^k$ and a permutation $\sigma$ of $[k]$, the permutation $\pi_{z,\sigma}$ of $[2k]$ is
--   $$\pi_{z,\sigma}(2(k+1-j)-1):=2\sigma(j)-1+z_{\sigma(j)},\qquad \pi_{z,\sigma}(2(k+1-j)):=2\sigma(j)-z_{\sigma(j)}\qquad(j\in[k]),$$
--   and $\tilde h_{z,\sigma}:=h_k^{\pi_{z,\sigma}}$.
--
--   These objects state the two simulation lemmas C.5 and C.8.
--
--   **Formalization Note** All indices are 0-based. In 0-based form $\sigma$ sends position $2a+b$ ($b\in\{0,1\}$) to $\pi(2(k-1-a)+b)$, and $\pi_{z,\sigma}$ sends position $2(k-1-j)+b$ (0-based $j$) to the element $2u+(b\oplus z_u)$ with $u=\sigma(j)$. Both are built as compositions of bijections, so they are permutations by construction; the lemmas `simPerm_p`, `simPerm_r`, `encodingPerm_p`, `encodingPerm_r` restate the displayed equations in 0-based form.
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Lemma C.5 (displayed z, σ), printed p. 21 / PDF p. 22; Definition C.7, printed p. 23 / PDF p. 24

import Definitions.Def_SFMQueryLower_EmptyMin_Supplement_CGJSFamily
import Definitions.Def_SFMQueryLower_EmptyMin_Supplement_HiddenPermutation

set_option autoImplicit false

namespace SFMQueryLower.EmptyMin.Supplement

/-- Lemma C.5's string `z ∈ {0,1}^n` (`n = 2k`): `z_{p_i^π} = 1` and `z_{r_i^π} = 0` for every
`i`. Every element of `[2k]` is some `p_i^π` or `r_i^π`, so this is the indicator of `P^π`. -/
def simString {k : ℕ} (π : Equiv.Perm (Fin (2 * k))) : Fin (2 * k) → Bool :=
  fun v => decide (v ∈ cgjsMinimizer π)

/-- Lemma C.5's permutation `σ` of `[n]`: `σ(2(k − i) + 1) = p_i^π`, `σ(2(k − i) + 2) = r_i^π`
(1-based). In 0-based form, position `2 a + b` is sent to `π(2 (k − 1 − a) + b)`. -/
def simPerm {k : ℕ} (π : Equiv.Perm (Fin (2 * k))) : Equiv.Perm (Fin (2 * k)) :=
  (pairEquiv k).symm.trans
    ((Equiv.prodCongr Fin.revPerm (Equiv.refl Bool)).trans ((pairEquiv k).trans π))

/-- The displayed definition of `σ` in Lemma C.5, 0-based: for source layer `i = l + 1`,
the 0-based position `2(k − i)` is `2 · rev(l)`. -/
theorem simPerm_p {k : ℕ} (π : Equiv.Perm (Fin (2 * k))) (l : Fin k) :
    simPerm π (pairEquiv k (Fin.rev l, false)) = cgjsP π l := by
  simp [simPerm, cgjsP]

theorem simPerm_r {k : ℕ} (π : Equiv.Perm (Fin (2 * k))) (l : Fin k) :
    simPerm π (pairEquiv k (Fin.rev l, true)) = cgjsR π l := by
  simp [simPerm, cgjsR]

/-- Bit flip `b ↦ 1 − b` as a permutation of `Bool`. -/
def flipBool : Equiv.Perm Bool := Function.Involutive.toPerm (fun b : Bool => !b) Bool.not_not

@[simp] theorem flipBool_apply (b : Bool) : flipBool b = !b := rfl

/-- Definition C.7: `π_{z,σ}(2(k+1−j) − 1) = 2σ(j) − 1 + z_{σ(j)}` and
`π_{z,σ}(2(k+1−j)) = 2σ(j) − z_{σ(j)}` (1-based). In 0-based form, with `j` 0-based and
`u = σ(j)`, position `2 (k − 1 − j) + b` goes to element `2u + (b xor z_u)`. Built as a
composition of bijections, so it is a permutation of `[2k]` by construction. -/
def encodingPerm {k : ℕ} (z : Fin k → Bool) (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin (2 * k)) :=
  (pairEquiv k).symm.trans
    ((Equiv.prodShear (Fin.revPerm.trans σ)
      (fun a => if z (σ (Fin.rev a)) then flipBool else Equiv.refl Bool)).trans (pairEquiv k))

/-- The first displayed equation of Definition C.7, 0-based. -/
theorem encodingPerm_p {k : ℕ} (z : Fin k → Bool) (σ : Equiv.Perm (Fin k)) (j : Fin k) :
    ((encodingPerm z σ (pairEquiv k (Fin.rev j, false))).val : ℕ) =
      2 * (σ j).val + (if z (σ j) then 1 else 0) := by
  cases h : z (σ j) <;> simp [encodingPerm, h]

/-- The second displayed equation of Definition C.7, 0-based. -/
theorem encodingPerm_r {k : ℕ} (z : Fin k → Bool) (σ : Equiv.Perm (Fin k)) (j : Fin k) :
    ((encodingPerm z σ (pairEquiv k (Fin.rev j, true))).val : ℕ) =
      2 * (σ j).val + (if z (σ j) then 0 else 1) := by
  cases h : z (σ j) <;> simp [encodingPerm, h]

/-- Definition C.7: `h̃_{z,σ} := h_k^{π_{z,σ}}`. -/
noncomputable def encodedFunction {k : ℕ} (z : Fin k → Bool) (σ : Equiv.Perm (Fin k)) :
    Finset (Fin (2 * k)) → ℝ :=
  cgjsFunction (encodingPerm z σ)

end SFMQueryLower.EmptyMin.Supplement


