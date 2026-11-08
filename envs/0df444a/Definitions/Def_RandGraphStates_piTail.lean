-- Prove2me | Definitions.Def_RandGraphStates_piTail
-- name    : RandGraphStates_piTail
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:22.803626+00:00
-- url     : https://prove2.me/theorems/586bbb81-a5d4-47e7-a316-adb6d0a2c1b3
-- title:
--   The tails $\pi^p_m(t)$, $\Pi^p_k(t)$, $\mathrm{Ber}(p)$ weights and the conditional block tail
-- statement:
--   Let $A_m(p)$ be the adjacency matrix of $G_{m,p}$ over $\mathbb F_2$. Over diagonal matrices $D$ with entries in $\{0,1\}$, and over fixed symmetric $k\times k$ matrices $\Gamma$ with zero diagonal, define
--   $$
--   \pi^p_m(t):=\sup_{D}\Pr\bigl(\mathrm{Nullity}(A_m(p)+D)\ge t\bigr),\qquad
--   \Pi^p_k(t):=\sup_{\Gamma}\Pr\bigl(\mathrm{Nullity}(A_k(p)+\Gamma)\ge t\bigr).
--   $$
--   A vector with independent $\mathrm{Ber}(p)$ coordinates has law $\prod_i p^{x_i}(1-p)^{1-x_i}$. For a fixed symmetric $M_k$ and a prescribed diagonal $b$, the block tail is
--   $$
--   \Pr\bigl(\mathrm{Nullity}\bigl[\begin{smallmatrix}M_k&Y\\Y^{T}&A_s(p)+\mathrm{diag}(b)\end{smallmatrix}\bigr]\ge t\ \big|\ M_k\bigr),
--   $$
--   with $Y$ having independent $\mathrm{Ber}(p)$ entries, independent of $A_s(p)$. These are the quantities every nullity estimate of the mission bounds.
--
--   **Formalization Note** The threshold is a natural number. At $t=0$ the event is everything and the value is $1$, which is the paper's convention for $t\le0$. Both suprema range over finite nonempty types. Conditioning on $M_k$ is fixing it as a parameter. $G_{m,p}$ is the published `BollobasChromatic_Main_Setting`.
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), §4.1, p.18, §4.2.3, p.24, Lemma 4.5, p.21, Lemma 4.9, p.24, and Lemma 4.19, p.34

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting
import Definitions.Def_RandGraphStates_nullity

set_option autoImplicit false

open BollobasChromatic.Main

namespace RandGraphStates

/-- `π^p_m(t) := sup_{D ∈ D([m])} Pr(Nullity(A_m(p) + D) ≥ t)`, with `D` ranging over the diagonal
matrices with entries in `{0, 1}` and `A_m(p)` the adjacency matrix of `G_{m,p}`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript
(November 2026), §4.1, p.18.

**Formalization Note.** The threshold is `t : ℕ`; at `t = 0` the event is everything, so the value
is `1`, which is the paper's convention for `t ≤ 0`. The supremum is over a finite nonempty type. -/
noncomputable def piTail (p : ℝ) (m t : ℕ) : ℝ :=
  ⨆ d : Fin m → ZMod 2,
    gnpProb m p (fun G => t ≤ nullity (adjF2 G + Matrix.diagonal d))

/-- The fixed symmetric `k × k` matrices over `F₂` with zero diagonal. -/
abbrev ZeroDiagSymm (k : ℕ) : Type :=
  {Γ : Matrix (Fin k) (Fin k) (ZMod 2) // Γ.IsSymm ∧ ∀ i, Γ i i = 0}

/-- `Π^p_k(t) := sup_Γ Pr(Nullity(A_k(p) + Γ) ≥ t)`, over fixed symmetric `k × k` matrices `Γ` with
zero diagonal.

Source: ibid., §4.2.3, p.24.

**Formalization Note.** As for `piTail`, `t : ℕ`, and the value at `t = 0` is `1`. The supremum is
over a finite nonempty type (it contains `Γ = 0`). -/
noncomputable def bigPiTail (p : ℝ) (k t : ℕ) : ℝ :=
  ⨆ Γ : ZeroDiagSymm k,
    gnpProb k p (fun G => t ≤ nullity (adjF2 G + Γ.1))

/-- The law of a vector with independent `Ber(p)` coordinates, at the point `x`.

Source: ibid., Lemma 4.5, p.21. -/
noncomputable def berWeight {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ZMod 2) : ℝ :=
  ∏ i, if x i = 1 then p else 1 - p

/-- `Pr(Nullity(M) ≥ t | M_k)` for `M = [M_k Y; Yᵀ Z_s]`, where the `k × s` block `Y` has independent
`Ber(p)` entries, independent of the off-diagonal entries of `Z_s`, which are those of `A_s(p)`,
and the diagonal of `Z_s` is the prescribed vector `b`.

Source: ibid., Lemma 4.9, p.24, and Lemma 4.19, p.34.

**Formalization Note.** Conditioning on `M_k` is fixing it as a parameter: the sum runs over the
remaining entries only. -/
noncomputable def blockTail {k s : ℕ} (p : ℝ) (Mk : Matrix (Fin k) (Fin k) (ZMod 2))
    (b : Fin s → ZMod 2) (t : ℕ) : ℝ :=
  ∑ Y : Matrix (Fin k) (Fin s) (ZMod 2),
    berWeight p (fun ij : Fin k × Fin s => Y ij.1 ij.2) *
      gnpProb s p (fun G =>
        t ≤ nullity (Matrix.fromBlocks Mk Y Y.transpose (adjF2 G + Matrix.diagonal b)))

end RandGraphStates


