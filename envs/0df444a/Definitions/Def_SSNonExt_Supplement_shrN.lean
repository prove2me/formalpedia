-- Prove2me | Definitions.Def_SSNonExt_Supplement_shrN
-- name    : SSNonExt_Supplement_shrN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:56:33.425773+00:00
-- url     : https://prove2.me/theorems/253f1899-5ffa-454e-8f21-3edafdc91f4d
-- title:
--   The two-out-of-$n$ scheme $\Pi_{b,n}$: keys $\mathcal K_n$, shares (5) and sources $P_T$, $\mathcal S_{b,n}$ (6)
-- statement:
--   Let $n\ge2$, $V=\mathbb F_{2^b}$ and $B=2^b$, and let $\alpha_1,\dots,\alpha_n\in V$. For every index $i\in V$ there are $2n-1$ keys: $n-1$ **central keys** $C_i^{(1)},\dots,C_i^{(n-1)}$ and $n$ **side keys** $X_i^{(1)},\dots,X_i^{(n)}$, so that
--
--   $$\mathcal K_n=\{C_i^{(c)}:c\in[n-1],\ i\in V\}\cup\{X_i^{(j)}:j\in[n],\ i\in V\},\qquad|\mathcal K_n|=(2n-1)B.$$
--
--   The share alphabet of every party is $\{0,1\}\times V$, where $x$ denotes the untagged value $(0,x)$ and $\bar x$ the tagged value $(1,x)$. The scheme $\Pi_{b,n}$ shares a message $m\in V$ by giving party $j\in[n]$ the share
--
--   $$\mathrm{Shr}_j(m,C_i^{(c)})=\alpha_j i+m,\qquad \mathrm{Shr}_j(m,X_i^{(j')})=\begin{cases}\bar i & j=j',\\ \alpha_j i+m & j\ne j'.\end{cases}$$
--
--   For $T\subseteq V$ the source $P_T$ is the uniform distribution on
--
--   $$\Omega_T=\{C_i^{(c)}:i\in T,\ c\in[n-1]\}\cup\{X_i^{(j)}:i\notin T,\ j\in[n]\},$$
--
--   and the source class is $\mathcal S_{b,n}=\{P_T:T\subseteq V\}$. The **index** of a key $C_i^{(c)}$ or $X_i^{(j)}$ is $i$.
--
--   This is the construction of Theorem 4.1; for $n=2$, $\alpha_1=1$, $\alpha_2=\alpha$ it is the scheme $\Pi_b$ and class $\mathcal S_b$ of §3.
--
--   **Formalization Note** $V$ and the share alphabet are the published `SSNonExt.V b` and `SSNonExt.Share b`. Central keys are `Sum.inl (c, i)` with `c : Fin (n-1)` and side keys `Sum.inr (j, i)` with `j : Fin n`; parties are `Fin n`, counted from $0$. The $n-1$ central keys at an index are distinct keys. $P_T$ takes the hypothesis $n\ge2$, which makes $\Omega_T$ nonempty for every $T$. The module also records that $\mathcal K_n$ is nonempty for $n\ge2$.
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), §4.1, displays (5) and (6), p.8 (PDF p.8)

import Mathlib
import Definitions.Def_SSNonExt_scheme

namespace SSNonExt.Supplement

open SSNonExt

/-- The key set `𝒦_n = {C_i^{(c)} : c ∈ [n−1], i ∈ V} ∪ {X_i^{(j)} : j ∈ [n], i ∈ V}` of §4.1 (p.8).
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), §4.1, p.8 (PDF p.8).

**Formalization Note.** `Sum.inl (c, i)` is the central key `C_i^{(c+1)}` (`c : Fin (n − 1)`) and
`Sum.inr (j, i)` is the side key `X_i^{(j+1)}` (`j : Fin n`); indices `[n−1]`, `[n]` are counted from
`0`. The `n − 1` central keys at one index are distinct keys. -/
abbrev KeyN (b n : ℕ) : Type := (Fin (n - 1) × V b) ⊕ (Fin n × V b)

/-- The index `i ∈ V` of a key `C_i^{(c)}` or `X_i^{(j)}` (§4.1, p.8). -/
def keyIndexN {b n : ℕ} : KeyN b n → V b
  | Sum.inl (_, i) => i
  | Sum.inr (_, i) => i

/-- The scheme `Π_{b,n}` of display (5), p.8: party `j` receives
`Shr_j(m, C_i^{(c)}) = α_j i + m`, `Shr_j(m, X_i^{(j′)}) = ī` (tagged `i`) if `j = j′` and
`α_j i + m` if `j ≠ j′`.
arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), §4.1, display (5), p.8.

**Formalization Note.** A sharing map in the format of Definition 2.1 (`SSNonExt.shrJ`):
`shrN α m k j` is party `j`'s share, in the alphabet `Share b = {0,1} × V`, `(false, x)` untagged `x`,
`(true, x)` tagged `x̄`. The elements `α_1, …, α_n` are the function `α : Fin n → V b`. -/
noncomputable def shrN {b n : ℕ} (α : Fin n → V b) (m : V b) : KeyN b n → Fin n → Share b
  | Sum.inl (_, i), j => (false, α j * i + m)
  | Sum.inr (j', i), j => if j = j' then (true, i) else (false, α j * i + m)

/-- The support `Ω_T = {C_i^{(c)} : i ∈ T, c ∈ [n−1]} ∪ {X_i^{(j)} : i ∉ T, j ∈ [n]}` of display (6),
p.8: all central keys at indices in `T`, all side keys at indices outside `T`.
`Finset.disjSum A B` is the set `{inl a : a ∈ A} ∪ {inr b : b ∈ B}`.
arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), §4.1, display (6), p.8. -/
noncomputable def OmegaN {b n : ℕ} (T : Finset (V b)) : Finset (KeyN b n) :=
  (Finset.univ ×ˢ T).disjSum (Finset.univ ×ˢ Tᶜ)

/-- For `n ≥ 2`, `Ω_T` is nonempty: it contains `C_0^{(1)}` if `0 ∈ T` and `X_0^{(1)}` otherwise. -/
theorem OmegaN_nonempty {b n : ℕ} (hn : 2 ≤ n) (T : Finset (V b)) :
    (OmegaN (n := n) T).Nonempty := by
  by_cases h : (0 : V b) ∈ T
  · exact ⟨Sum.inl (⟨0, by omega⟩, 0), by simp [OmegaN, Finset.mem_disjSum, h]⟩
  · exact ⟨Sum.inr (⟨0, by omega⟩, 0), by simp [OmegaN, Finset.mem_disjSum, h]⟩

/-- The source `P_T = U_{Ω_T}` of display (6), p.8 (uniform on `Ω_T`). -/
noncomputable def srcPN {b n : ℕ} (hn : 2 ≤ n) (T : Finset (V b)) : PMF (KeyN b n) :=
  PMF.uniformOfFinset (OmegaN T) (OmegaN_nonempty hn T)

/-- The source class `𝒮_{b,n} = {P_T : T ⊆ V}` (§4.1, p.8). It depends neither on `α`, on the
message nor on any extractor. -/
def srcClassN {b n : ℕ} (hn : 2 ≤ n) : Set (PMF (KeyN b n)) :=
  Set.range (srcPN (b := b) hn)

/-- For `n ≥ 2` the key set `𝒦_n` is nonempty (needed to speak of the min-entropy of a source on it). -/
theorem keyN_nonempty {b n : ℕ} (hn : 2 ≤ n) : Nonempty (KeyN b n) :=
  ⟨Sum.inr (⟨0, by omega⟩, 0)⟩

end SSNonExt.Supplement


