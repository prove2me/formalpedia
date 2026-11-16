-- Prove2me | Definitions.Def_SSNonExt_Supplement_shrR
-- name    : SSNonExt_Supplement_shrR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:57:13.243988+00:00
-- url     : https://prove2.me/theorems/036f4cb9-b430-46dd-846b-03efb4bd2aba
-- title:
--   The $r$-out-of-$r$ scheme $\Pi_b^{(r)}$: pads, keys $\mathcal K^{(r)}$, shares (7) and sources $P_T$, $\mathcal S_b^{(r)}$ (8)
-- statement:
--   Let $r\ge2$, $V=\mathbb F_{2^b}$, $B=2^b$, $N=B^{r-1}$, and let $\gamma_1,\dots,\gamma_r\in V$. The index is a vector $u=(u_1,\dots,u_{r-1})\in V^{r-1}$, and the **pad** of party $j$ is
--
--   $$p_j(u)=u_j\ (j<r),\qquad p_r(u)=u_1+\dots+u_{r-1}.$$
--
--   A key is a pair $(u,S)$ with $u\in V^{r-1}$ and $\emptyset\ne S\subseteq[r]$; $\mathcal K^{(r)}$ is the set of keys. The scheme $\Pi_b^{(r)}$ shares $m\in V$ as
--
--   $$\mathrm{Shr}_j(m,(u,S))=\begin{cases}p_j(u)+\gamma_j m & j\in S,\\ \overline{p_j(u)} & j\notin S,\end{cases}$$
--
--   so an active party ($j\in S$) receives its pad plus a multiple of the secret, untagged, and an inactive party receives its pad, tagged, as a dummy. Let $\mathcal O_r$ be the family of subsets of $[r]$ of odd size and $\mathcal E_r$ the family of nonempty subsets of even size. For $T\subseteq V^{r-1}$ the source $P_T$ is uniform on
--
--   $$\Omega_T=\{(u,S):u\in T,\ S\in\mathcal O_r\}\cup\{(u,S):u\notin T,\ S\in\mathcal E_r\},$$
--
--   and the source class is $\mathcal S_b^{(r)}=\{P_T:T\subseteq V^{r-1}\}$. The index of a key $(u,S)$ is $u$.
--
--   This is the construction of Theorem 5.1. Note that indices in $T$ carry the larger family (the odd sets).
--
--   **Formalization Note** $V$ and the share alphabet $\{0,1\}\times V$ are the published `SSNonExt.V b` and `SSNonExt.Share b`; $(1,x)$ is the tagged $\bar x$. The index is `Fin (r-1) → V b` and $S$ a nonempty `Finset (Fin r)`; parties are counted from $0$, so the last party $r-1$ gets $\sum_i u_i$. The overline on the inactive share is printed on the page (the text layer loses it). $P_T$ takes the hypothesis $r\ge2$, which makes $\Omega_T$ nonempty.
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), §5, pads, displays (7) and (8), p.10 (PDF p.10)

import Mathlib
import Definitions.Def_SSNonExt_scheme

namespace SSNonExt.Supplement

open SSNonExt

/-- The key set `𝒦^{(r)} = {(u, S) : u ∈ V^{r−1}, ∅ ≠ S ⊆ [r]}` of §5 (p.10).
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), §5, p.10 (PDF p.10).

**Formalization Note.** The index `u = (u_1, …, u_{r−1})` is `Fin (r − 1) → V b` and the set of active
parties `S` is a nonempty `Finset (Fin r)`; parties `1, …, r` are `0, …, r − 1`. -/
abbrev KeyR (b r : ℕ) : Type := (Fin (r - 1) → V b) × {S : Finset (Fin r) // S.Nonempty}

/-- The pads of §5, p.10: `p_j(u) = u_j` for `j < r` and `p_r(u) = u_1 + ⋯ + u_{r−1}`.
arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), §5, p.10.

**Formalization Note.** With parties indexed from `0`, party `j` with `j < r − 1` gets `u_j` and the
last party `r − 1` gets `∑ u`. -/
noncomputable def pad {b r : ℕ} (j : Fin r) (u : Fin (r - 1) → V b) : V b :=
  if h : j.val < r - 1 then u ⟨j.val, h⟩ else ∑ i, u i

/-- The scheme `Π_b^{(r)}` of display (7), p.10:
`Shr_j(m, (u, S)) = p_j(u) + γ_j m` (untagged) if `j ∈ S`, and `\overline{p_j(u)}` (tagged) if `j ∉ S`.
arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), §5, display (7), p.10.

**Formalization Note.** The overline on the inactive share is printed on the page (the text layer
drops it) and the prose after (7) says "an inactive party receives its pad, tagged, as a dummy"; it is
`(true, p_j(u))` in `Share b = {0,1} × V`. The elements `γ_1, …, γ_r` are `γ : Fin r → V b`. -/
noncomputable def shrR {b r : ℕ} (γ : Fin r → V b) (m : V b) : KeyR b r → Fin r → Share b :=
  fun k j => if j ∈ k.2.1 then (false, pad j k.1 + γ j * m) else (true, pad j k.1)

/-- The index `u` of a key `(u, S)` (§5, p.10). -/
def keyIndexR {b r : ℕ} (k : KeyR b r) : Fin (r - 1) → V b := k.1

/-- The support of display (8), p.10:
`Ω_T = {(u, S) : u ∈ T, S ∈ 𝒪_r} ∪ {(u, S) : u ∉ T, S ∈ ℰ_r}`, where `𝒪_r` is the family of subsets of
`[r]` of odd size and `ℰ_r` the family of nonempty subsets of even size.
arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), §5, display (8), p.10.

**Formalization Note.** Every key's set is nonempty by the type `KeyR`, so "even size" here is
"nonempty and even size". As printed, indices in `T` carry the odd sets. -/
noncomputable def OmegaR {b r : ℕ} (T : Finset (Fin (r - 1) → V b)) : Finset (KeyR b r) :=
  Finset.univ.filter fun k => if k.1 ∈ T then Odd k.2.1.card else Even k.2.1.card

/-- For `r ≥ 2`, `Ω_T` is nonempty: at the index `0` it contains `({1}, 0)` if `0 ∈ T` and
`({1, 2}, 0)` otherwise. -/
theorem OmegaR_nonempty {b r : ℕ} (hr : 2 ≤ r) (T : Finset (Fin (r - 1) → V b)) :
    (OmegaR (r := r) T).Nonempty := by
  classical
  by_cases h : (0 : Fin (r - 1) → V b) ∈ T
  · refine ⟨(0, ⟨{⟨0, by omega⟩}, Finset.singleton_nonempty _⟩), ?_⟩
    simp [OmegaR, h]
  · refine ⟨(0, ⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, Finset.insert_nonempty _ _⟩), ?_⟩
    have hne : (⟨0, by omega⟩ : Fin r) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    simp [OmegaR, h, Finset.card_pair hne]

/-- The source `P_T = U_{Ω_T}` of display (8), p.10. -/
noncomputable def srcPR {b r : ℕ} (hr : 2 ≤ r) (T : Finset (Fin (r - 1) → V b)) : PMF (KeyR b r) :=
  PMF.uniformOfFinset (OmegaR T) (OmegaR_nonempty hr T)

/-- The source class `𝒮_b^{(r)} = {P_T : T ⊆ V^{r−1}}` (§5, p.10). -/
def srcClassR {b r : ℕ} (hr : 2 ≤ r) : Set (PMF (KeyR b r)) :=
  Set.range (srcPR (b := b) hr)

/-- For `r ≥ 2` (indeed `r ≥ 1`) the key set `𝒦^{(r)}` is nonempty. -/
theorem keyR_nonempty {b r : ℕ} (hr : 2 ≤ r) : Nonempty (KeyR b r) :=
  ⟨(0, ⟨{⟨0, by omega⟩}, Finset.singleton_nonempty _⟩)⟩

end SSNonExt.Supplement


