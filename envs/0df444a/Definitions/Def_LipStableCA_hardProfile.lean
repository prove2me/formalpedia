-- Prove2me | Definitions.Def_LipStableCA_hardProfile
-- name    : LipStableCA_hardProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:25.292048+00:00
-- url     : https://prove2.me/theorems/e0c9db3c-22e9-40fe-9cf2-0487cce76561
-- title:
--   The family of hard profiles of the lower bound
-- statement:
--   Let $m\ge 32$, $0<\epsilon\le 1/16$, $c_0=1-h_2(1/4)$, $r=\lfloor m/2\rfloor$, $k=\lfloor c_0r\rfloor$. The items form $r$ pairs, with one item left over if $m$ is odd. A word $z^b\in\{0,1\}^r$ selects one item per pair, the set $B_b$. $G_b$ is the good allocation giving $B_b$ to bidder 1 and $M\setminus B_b$ to bidder 2. The bonus is $\beta^\sigma_b=\frac{16\epsilon}k(k-\mathrm{Ham}(b,\sigma))$, and the valuations are
--   $$v^\sigma_1(Q)=\begin{cases}0&|Q|<r\\1+\beta^\sigma_b&Q=B_b\text{ for some }b\\1&|Q|=r,\ Q\notin\{B_b\}\\1+16\epsilon&|Q|>r\end{cases}\qquad v_2(Q)=\mathbf 1\{M\setminus B_b\subseteq Q\text{ for some }b\}.$$
--   The decoding $\mathrm{dec}(S)$ is $b$ for $S=G_b$, and $(0,\dots,0)$ for $S$ not good; $e_\ell(\sigma)=\Pr_{S\sim P^\sigma}[\mathrm{dec}(S)_\ell\ne\sigma_\ell]$.
--
--   **Formalization Note.** Items are $o_{\ell,c}=2\ell+c$. The family is defined for an arbitrary $z$ and each statement assumes the code property of Claim 4.13, under which the chosen $b$ in $v_1^\sigma$ and $\mathrm{dec}$ is unique.
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), §4.3, pp.17–19, eq. (2)

import Definitions.Def_LipStableCA_emd

namespace LipStableCA

variable {m : ℕ}

/-- `c₀ = 1 − h₂(1/4)`, §4.3, p.17, with `h₂(p) = −p log₂ p − (1 − p) log₂(1 − p)`. -/
noncomputable def entropyGap : ℝ :=
  1 - (-(1 / 4) * Real.logb 2 (1 / 4) - (3 / 4) * Real.logb 2 (3 / 4))

/-- `r = ⌊m/2⌋`, §4.3, p.18. -/
def pairCount (m : ℕ) : ℕ := m / 2

/-- `k = ⌊c₀ r⌋`, §4.3, p.18. -/
noncomputable def codeLength (m : ℕ) : ℕ := ⌊entropyGap * (pairCount m : ℝ)⌋₊

/-- The binary codes `{0, 1}ᵏ`. -/
abbrev Code (m : ℕ) := Fin (codeLength m) → Bool

/-- The words `z^b ∈ {0, 1}ʳ` indexed by the codes `b`, §4.3, p.18. -/
abbrev CodeMap (m : ℕ) := Code m → Fin (pairCount m) → Bool

/-- The property of Claim 4.13, p.18: `Ham(z^b, z^b′) > r/4` for distinct `b`, `b′`. The family below is
defined for an arbitrary `z`, and every claim carries this hypothesis, so no existence is hidden in a
definition. It makes `b ↦ z^b` injective. -/
def IsCodeMap (z : CodeMap m) : Prop :=
  ∀ b b' : Code m, b ≠ b' → (pairCount m : ℝ) / 4 < (hammingDist (z b) (z b') : ℝ)

open Classical in
/-- The set `B_b`, p.18. **Formalization Note.** Items are `Fin m`, with `o_{ℓ,c} = 2ℓ + c` for `ℓ < r`
and `c ∈ {0, 1}`, and the leftover item (`m` odd) is `2r`: `B_b` contains the first item of pair `ℓ` if
`z^b_ℓ = 0` and the second if `z^b_ℓ = 1`. -/
noncomputable def codeBundle (z : CodeMap m) (b : Code m) : Finset (Fin m) :=
  Finset.univ.filter fun j => ∃ l : Fin (pairCount m), j.val = 2 * l.val + (if z b l then 1 else 0)

/-- The bonus `β^σ_b = (16ϵ/k)(k − Ham(b, σ))`, p.18. -/
noncomputable def bonus (ϵ : ℝ) (σ b : Code m) : ℝ :=
  16 * ϵ / (codeLength m : ℝ) * ((codeLength m : ℝ) - (hammingDist b σ : ℝ))

open Classical in
/-- The valuation `v^σ₁`, eq. (2), p.18. **Formalization Note.** "`1 + β^σ_b` if `Q = B_b` for some `b`"
uses a chosen `b`, which is the only one under `IsCodeMap z`. -/
noncomputable def hardValuation₁ (z : CodeMap m) (ϵ : ℝ) (σ : Code m) (Q : Finset (Fin m)) : ℝ :=
  if Q.card < pairCount m then 0
  else if pairCount m < Q.card then 1 + 16 * ϵ
  else if h : ∃ b, Q = codeBundle z b then 1 + bonus ϵ σ h.choose
  else 1

open Classical in
/-- The valuation `v₂(Q) = 1{M ∖ B_b ⊆ Q for some b}`, p.18. -/
noncomputable def hardValuation₂ (z : CodeMap m) (Q : Finset (Fin m)) : ℝ :=
  if ∃ b, Finset.univ \ codeBundle z b ⊆ Q then 1 else 0

/-- The profile `v^σ = (v^σ₁, v₂)` on two bidders, p.18. -/
noncomputable def hardProfile (z : CodeMap m) (ϵ : ℝ) (σ : Code m) : Profile 2 m :=
  ![hardValuation₁ z ϵ σ, hardValuation₂ z]

/-- The good allocation `G_b`, p.18: `B_b` to bidder 1 and `M ∖ B_b` to bidder 2. -/
noncomputable def goodAlloc (z : CodeMap m) (b : Code m) : Alloc 2 m :=
  ⟨![codeBundle z b, Finset.univ \ codeBundle z b], by
    intro i i' h
    fin_cases i <;> fin_cases i' <;> first
      | exact absurd rfl h
      | simpa using Finset.disjoint_sdiff
      | simpa using Finset.sdiff_disjoint⟩

/-- `S` is good, p.18. -/
def IsGood (z : CodeMap m) (S : Alloc 2 m) : Prop := ∃ b, S = goodAlloc z b

open Classical in
/-- `dec(S)`, p.19: `dec(G_b) = b` and `dec(S) = (0, …, 0)` for `S` not good. **Formalization Note.** The
chosen `b` is the only one under `IsCodeMap z`. -/
noncomputable def decode (z : CodeMap m) (S : Alloc 2 m) : Code m :=
  if h : IsGood z S then h.choose else fun _ => false

open Classical in
/-- `e_ℓ(σ) = Pr_{S∼P}[dec(S)_ℓ ≠ σ_ℓ]`, p.19, for a law `P`. -/
noncomputable def decodeError (z : CodeMap m) (P : Alloc 2 m → ℝ) (σ : Code m)
    (l : Fin (codeLength m)) : ℝ :=
  ∑ S, if decode z S l ≠ σ l then P S else 0

end LipStableCA


