-- Prove2me | Definitions.Def_DSICHardRev_ReductionClass
-- name    : DSICHardRev_ReductionClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:35:46.201231+00:00
-- url     : https://prove2.me/theorems/457771bd-2a50-4ec6-84dc-63d8d171e19e
-- title:
--   The valuation classes $\mathcal V(\mathcal H)$, $v_{s,t}$, $v_{s,t,X,Y}$ and $\mathcal V[s^-,s^+](\mathcal H)$
-- statement:
--   Let $\mathcal H$ be a KSSHD on the regular items $[m]$ and add a special item $\dagger$, so that $M=[m]\cup\{\dagger\}$.
--
--   1. $\mathcal V(\mathcal H)$ consists of the zero valuation and every item-relabeled $u_x\in\mathcal U$, i.e. $S\mapsto u_x(\varphi^{-1}(S))$ for an injection $\varphi:[\beta]\to[m]$.
--   2. If $\mathcal H$ uses GS or XOS valuations, for $v\in\mathcal V(\mathcal H)$, $s\in\mathbb R$, $t\ge0$,
--   $$v_{s,t}(S)=2^{s/2}\Big(v(S\cap[m])+(\alpha\eta+t/m)\,\mathbb 1(\dagger\in S)\Big).$$
--   3. If $\mathcal H$ uses general valuations, for nonempty $X,Y\subseteq M$,
--   $$v_{s,t,X,Y}(S)=2^{s/2}\Big(v(S\cap[m])\,\mathbb 1(S\not\supseteq X\wedge S\not\supseteq Y)+(2\alpha+t/m)\,\mathbb 1(S\supseteq X\vee S\supseteq Y)\Big),$$
--   and $v_{s,t}=v_{s,t,M,M}$.
--   4. $\mathcal V[s^-,s^+](\mathcal H)$ is the set of these valuations with $s\in\mathbb Z\cap[s^-,s^+]$, $t\in\mathbb Z\cap[0,m^4]$, $v\in\mathcal V(\mathcal H)$ (and nonempty $X,Y$ in the general case).
--
--   These are the domains on which DSIC mechanisms are converted into simultaneous algorithms in Section 4.
--
--   **Formalization Note** Items are `Option (Fin m)` with `none` the special item $\dagger$. One function `vst` gives $v_{s,t}$ for GS/XOS KSSHDs (ignoring $X,Y$) and $v_{s,t,X,Y}$ for general ones; `vst0` is $v_{s,t}$.
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §4.1, pp.16–17

import Mathlib
import Definitions.Def_DSICHardRev_KSSHD

namespace DSICHardRev

/-!
# The valuation classes `V(H)` and `V[s⁻, s⁺](H)` of the DSIC reduction

F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §4.1, pp.16–17.

**Formalization Note.**
* Items are `Option (Fin m)`: `some j` is the regular item `j ∈ [m]` on which the KSSHD lives and
  `none` is the special item `†`; `M = [m] ∪ {†}`. Here `m` is the number of **regular** items.
* `V(H)` (`VH`) consists of the zero valuation and every item-relabeled `u_x ∈ U`:
  `S ↦ u_x(φ^{-1}(S))` for `x ∈ {0,1,2}^λ` and an injection `φ : [β] ↪ [m]`.
* `vst v s t X Y` is `v_{s,t}` for GS/XOS KSSHDs,
  `v_{s,t}(S) = 2^{s/2}(v(S ∩ [m]) + (αη + t/m) · 1(† ∈ S))` (X, Y unused), and `v_{s,t,X,Y}` for
  general KSSHDs,
  `2^{s/2}(v(S ∩ [m]) · 1(S ⊉ X ∧ S ⊉ Y) + (2α + t/m) · 1(S ⊇ X ∨ S ⊇ Y))`. `vst0 v s t` is
  `v_{s,t}`, which for general valuations abbreviates `v_{s,t,M,M}`.
* `Vrange s⁻ s⁺` is `V[s⁻, s⁺](H)`: `s ∈ ℤ ∩ [s⁻, s⁺]`, `t ∈ ℤ ∩ [0, m⁴]`, `v ∈ V(H)`, and, for
  general KSSHDs, nonempty `X, Y ⊆ M` (for GS/XOS KSSHDs the sets are irrelevant).
-/

namespace KSSHD

variable {m : ℕ} (H : KSSHD m)

/-- The regular items of a bundle: `S ∩ [m]`. -/
def reg (S : Finset (Option (Fin m))) : Finset (Fin m) :=
  Finset.univ.filter fun j => some j ∈ S

/-- `V(H)`: the zero valuation and every item-relabeled `u_x ∈ U`. -/
def VH : Set (Finset (Fin m) → ℝ) :=
  {v | v = 0 ∨ ∃ (x : Fin H.lam → Fin 3) (φ : Fin H.β ↪ Fin m),
    v = fun S => (H.u x (Finset.univ.filter fun c => φ c ∈ S) : ℝ)}

/-- `v_{s,t}` (GS/XOS KSSHDs) or `v_{s,t,X,Y}` (general KSSHDs) on the items `[m] ∪ {†}`. -/
noncomputable def vst (v : Finset (Fin m) → ℝ) (s t : ℝ) (X Y : Finset (Option (Fin m)))
    (S : Finset (Option (Fin m))) : ℝ :=
  match H.branch with
  | .gen => (2 : ℝ) ^ (s / 2) *
      (v (reg S) * (if ¬ X ⊆ S ∧ ¬ Y ⊆ S then 1 else 0) +
        (2 * (H.α : ℝ) + t / m) * (if X ⊆ S ∨ Y ⊆ S then 1 else 0))
  | _ => (2 : ℝ) ^ (s / 2) *
      (v (reg S) + ((H.α : ℝ) * H.η + t / m) * (if none ∈ S then 1 else 0))

/-- `v_{s,t}`; for general KSSHDs this is `v_{s,t,M,M}`. -/
noncomputable def vst0 (v : Finset (Fin m) → ℝ) (s t : ℝ) : Finset (Option (Fin m)) → ℝ :=
  H.vst v s t Finset.univ Finset.univ

/-- `V[s⁻, s⁺](H)`. -/
def Vrange (sm sp : ℤ) : Set (Finset (Option (Fin m)) → ℝ) :=
  {w | ∃ v ∈ H.VH, ∃ s : ℤ, sm ≤ s ∧ s ≤ sp ∧ ∃ t : ℤ, 0 ≤ t ∧ t ≤ (m : ℤ) ^ 4 ∧
    ∃ X Y : Finset (Option (Fin m)), X.Nonempty ∧ Y.Nonempty ∧ w = H.vst v s t X Y}

end KSSHD

end DSICHardRev


