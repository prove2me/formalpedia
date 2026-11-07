-- Prove2me | Definitions.Def_OnlineCAP_candFamily
-- name    : OnlineCAP_candFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:36.853816+00:00
-- url     : https://prove2.me/theorems/ee90e032-e17b-4a04-bdc4-be0a92ea2a83
-- title:
--   The family F of candidate query sets
-- statement:
--   Fix activation times $\tau_e\in\mathbb N$ for the virtual points and place the copy $e=(p,i)$ of $p=(u_p,v_p)$ at $(u_p,v_p,\tau_e)\in\mathbb R^3$. The family $\mathcal F$ of **candidate query sets** consists of the sets
--
--   1. $T_{\mathrm{leaf}}=\{e\in\pi^{-1}(S_u) : x(e)\ge a,\ y(e)\le c,\ \tau_e\le t\}$ for a leaf $u$;
--   2. $T_{\mathrm{left}}=\{e\in\pi^{-1}(S_{u_\ell}) : x(e)\ge a,\ y(e)\le c,\ \tau_e\le t\}$ and $T_{\mathrm{right}}=\{e\in\pi^{-1}(S_{u_r}) : x(e)\le b,\ y(e)\le c,\ \tau_e\le t\}$ for an internal node $u$ with children $u_\ell,u_r$,
--
--   over all nodes $u$ of the range tree and all $a,b,c\in\mathbb R$, $t\in\mathbb N$. Each is the set of virtual points of one node lying in an octant of $\mathbb R^3$.
--
--   **Formalization Note** $\tau$ is arbitrary; with the activation times of a run of Algorithm 2 (Definition 4.6), $\tau_e\le t$ means that $e$ is active at time $t$, and $\mathcal F$ contains every query the algorithm sends.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Lemma 4.7, p.18; proof of Lemma 4.7, p.19

import Mathlib
import Definitions.Def_OnlineCAP_VirtualPt
import Definitions.Def_OnlineCAP_xrank
import Definitions.Def_OnlineCAP_IsNode
import Definitions.Def_OnlineCAP_nodeSet

namespace OnlineCAP

/-- **The family of candidate query sets.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Lemma 4.7, p.18 and proof of Lemma 4.7, p.19
(PDF p.19): "Let F denote the family of all candidate query sets Qt ⊆ 𝒫 that can be generated
across all nodes of the range tree", with, for an internal node `u` with children `uℓ, ur`,
"Tleft = {s ∈ π−1(Suℓ) | sx ≥ at and sy ≤ ct and sz ≤ t}", "Tright = {s ∈ π−1(Sur) | sx ≤ bt and
sy ≤ ct and sz ≤ t}", and for a leaf `u`, "Tleaf = {s ∈ π−1(Su) | sx ≥ at and sy ≤ ct and
sz ≤ t}", where a copy `e = (p, i)` sits at `(u_p, v_p, τ_e) ∈ ℝ³`.

Given activation times `τ : 𝒫 → ℕ`, `candFamily P τ` is the family of all sets
1. `{e ∈ π⁻¹(S_u) : x(e) ≥ a, y(e) ≤ c, τ_e ≤ t}` for a leaf `u`;
2. `{e ∈ π⁻¹(S_{uℓ}) : x(e) ≥ a, y(e) ≤ c, τ_e ≤ t}` and
   `{e ∈ π⁻¹(S_{ur}) : x(e) ≤ b, y(e) ≤ c, τ_e ≤ t}` for an internal node `u`,

over all nodes and all `a, b, c ∈ ℝ`, `t ∈ ℕ`.

**Formalization Note.** `τ` is an arbitrary function, which covers the activation times
(Definition 4.6) of every run of Algorithm 2; with them, `τ_e ≤ t` iff `e` is active at time `t`. -/
noncomputable def candFamily (P : Finset (ℝ × ℝ)) (τ : VirtualPt P → ℕ) :
    Set (Finset (VirtualPt P)) := by
  classical
  exact {Q | ∃ h j : ℕ, IsNode P h j ∧ ∃ (a b c : ℝ) (t : ℕ),
    (h = 0 ∧ Q = Finset.univ.filter (fun e : VirtualPt P =>
        e.1 ∈ nodeSet P 0 j ∧ a ≤ e.1.1.1 ∧ e.1.1.2 ≤ c ∧ τ e ≤ t)) ∨
    (0 < h ∧ Q = Finset.univ.filter (fun e : VirtualPt P =>
        e.1 ∈ nodeSet P (h - 1) (2 * j) ∧ a ≤ e.1.1.1 ∧ e.1.1.2 ≤ c ∧ τ e ≤ t)) ∨
    (0 < h ∧ Q = Finset.univ.filter (fun e : VirtualPt P =>
        e.1 ∈ nodeSet P (h - 1) (2 * j + 1) ∧ e.1.1.1 ≤ b ∧ e.1.1.2 ≤ c ∧ τ e ≤ t))}

end OnlineCAP


