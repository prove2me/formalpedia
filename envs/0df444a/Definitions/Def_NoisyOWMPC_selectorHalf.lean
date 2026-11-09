-- Prove2me | Definitions.Def_NoisyOWMPC_selectorHalf
-- name    : NoisyOWMPC_selectorHalf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:49:51.926008+00:00
-- url     : https://prove2.me/theorems/f798ae2c-8322-4615-a721-029b18c4759f
-- title:
--   The subset selector of Construction 5.17 (protocol half)
-- statement:
--   For even $N$ put $r_N=\lfloor N^{0.51}\rfloor$, $q_0=2^{\lfloor0.26\log_2N\rfloor}$, $m=q_0-1$, $\bar N=\lfloor N/m\rfloor$, and let $t_{\mathrm{sel}}$ be an odd integer nearest to $N^{0.36}$. The segments $\mathcal N_1,\dots,\mathcal N_m$ are disjoint blocks of $\bar N$ positions of $[N]$. The **subset selector**: $\mathrm{Gen}_{\mathrm{sel}}$ samples independent uniform $t_{\mathrm{sel}}$-subsets $S_j\subseteq\mathcal N_j$; $\mathrm{Guard}_{\mathrm{sel}}(U)=\mathbf 1[\,||U|-N/2|\le r_N]$; and
--   $$b_{\mathcal S}(U)=\mathbf 1\Bigl[\sum_{j=1}^m\mathbf 1[|U\cap S_j|>t_{\mathrm{sel}}/2]>m/2\Bigr].$$
--
--   **Formalization Note** $t_{\mathrm{sel}}$ is the odd integer closest to $N^{0.36}$, the smaller one on a tie; $\mathcal N_j$ is the block $j\bar N,\dots,(j+1)\bar N-1$.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), §5.2.3, p.28; Construction 5.17, p.28

import Mathlib
import Definitions.Def_NoisyOWMPC_Halves

namespace NoisyOWMPC

/-- The balance slack `r_N = ⌊N^{0.51}⌋` (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256
3a9569fa…), §5.2.3 Parameters, p.28). -/
noncomputable def rN (N : ℕ) : ℕ := ⌊(N : ℝ) ^ ((51 : ℝ) / 100)⌋₊

/-- The power of two `q₀ = 2^{⌊0.26 log₂ N⌋}` (p.28). -/
noncomputable def q0 (N : ℕ) : ℕ := 2 ^ ⌊(26 / 100 : ℝ) * Real.logb 2 N⌋₊

/-- The row count `m = q₀ − 1` (p.28). -/
noncomputable def mSel (N : ℕ) : ℕ := q0 N - 1

/-- The segment size `N̄ = ⌊N/m⌋` (p.28). -/
noncomputable def Nbar (N : ℕ) : ℕ := N / mSel N

/-- The subset size `t_sel`, "an odd integer nearest to `N^{0.36}`" (p.28): the odd integer closest
to `N^{0.36}`, the smaller one on a tie. -/
noncomputable def tSel (N : ℕ) : ℕ :=
  let r : ℝ := (N : ℝ) ^ ((36 : ℝ) / 100)
  let a : ℕ := 2 * ⌊(r - 1) / 2⌋₊ + 1
  if |((a : ℝ) + 2) - r| < |(a : ℝ) - r| then a + 2 else a

/-- A selector key `S = (S_j)_{j ∈ [m]}`, `S_j` a `t_sel`-subset of the segment `N_j` (identified with
`[N̄]`) (Construction 5.17, p.28). -/
abbrev SelKey (N : ℕ) : Type := Fin (mSel N) → {S : Finset (Fin (Nbar N)) // S.card = tSel N}

open Classical in
/-- `|U ∩ S_j|`, where the segment `N_j` is the block of positions `j N̄, …, (j + 1) N̄ − 1` of `[N]`
(p.28: "Partition `m N̄` positions of `[N]` into disjoint segments `N₁, …, N_m` of size `N̄`"). -/
noncomputable def segCount (N : ℕ) (U : Finset (Fin N)) (j : Fin (mSel N))
    (S : Finset (Fin (Nbar N))) : ℕ :=
  (S.filter fun s => ∃ v ∈ U, v.val = j.val * Nbar N + s.val).card

open Classical in
/-- `Guard_sel(U) = 1[||U| − N/2| ≤ r_N]` (Construction 5.17, p.28). -/
noncomputable def selGuard (N : ℕ) (U : Finset (Fin N)) : Bool :=
  decide (|(U.card : ℝ) - (N : ℝ) / 2| ≤ (rN N : ℝ))

open Classical in
/-- The **majority of majorities** `b_S(U) = 1[∑_{j=1}^m 1[|U ∩ S_j| > t_sel/2] > m/2]`
(Construction 5.17, p.28). -/
noncomputable def selCoin (N : ℕ) (K : SelKey N) (U : Finset (Fin N)) : Bool :=
  decide (mSel N < 2 * (Finset.univ.filter fun j => tSel N < 2 * segCount N U j (K j).1).card)

open Classical in
/-- **Construction 5.17 (Subset selector), protocol half** (STOC 2027 submission (manuscript sha256
3a9569fa…), p.28): `Gen_sel(1^λ)` samples independent uniform `t_sel`-subsets `S_j ⊆ N_j`, the guard
is the balance check and the coin is the majority of majorities.

**Formalization Note** The key is uniform on `SelKey N`; it is encoded by the indicator vectors of
the `S_j`. -/
noncomputable def selectorHalf (N : ℕ → ℕ) : SelHalf N where
  Key lam := SelKey (N lam)
  genW lam := unifW _
  enc lam K := (List.ofFn fun j => List.ofFn fun s => decide (s ∈ (K j).1)).flatten
  guard lam U := selGuard (N lam) U
  coin lam K U := selCoin (N lam) K U

end NoisyOWMPC


