-- Prove2me | Definitions.Def_SamplingAC0_hardSampler
-- name    : SamplingAC0_hardSampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:46:34.91145+00:00
-- url     : https://prove2.me/theorems/af7d31f7-0326-4395-ae17-b9d131924884
-- title:
--   The padded DNF sampler of Theorem 4
-- statement:
--   For $q=2^k$ let $t=q^{13}$, $b=q^2+2qk$ and $n_0(k)=t\,b$. For $n\ge n_0(1)$ let $k=k(n)$ be the largest $k$ with $n_0(k)\le n$.
--
--   The **sampler of Theorem 4 on $n$ bits** uses $t$ blocks of $2qk$ uniform input bits. Its first $n_0(k)$ output positions are arranged, by one fixed bijection, as pairs (copy $r<t$, output position of $R$); output position $(r,p)$ is the DNF of the block sampler of $R$ at $p$ (the line DNF $C_\ell$, or a single input bit), read on the $r$-th input block. The remaining $n-n_0(k)$ outputs are the empty DNF, i.e. the constant $0$ (all outputs are $0$ when $n<n_0(1)$).
--
--   Its output distribution is $t$ independent copies of $R$ followed by constant zeros: "take $t:=q^{13}$ independent copies of $R$".
--
--   **Formalization Note** The padding to every $n$ and the fixed output layout are this formalization's construction (the paper states the distribution for one $n$ per $q$); forests are closed under permuting and dropping outputs, so the layout does not affect the separation.
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), §3, p.8 ("take t := q^13 independent copies of R"); Theorem 4, p.3

import Mathlib
import Definitions.Def_SamplingAC0_DNF
import Definitions.Def_SamplingAC0_lineDNF
set_option autoImplicit false

namespace SamplingAC0

/-- `n₀(k) = t · b` with `q = 2^k`, `t = q^{13}` copies and `b = q² + 2qk` bits per copy. -/
def n₀ (k : ℕ) : ℕ := 2 ^ (13 * k) * (2 ^ (2 * k) + 2 * 2 ^ k * k)

/-- The largest `k ≤ n` with `n₀(k) ≤ n` (it is `≥ 1` once `n ≥ n₀(1)`). -/
def kOf (n : ℕ) : ℕ := Nat.findGreatest (fun k => n₀ k ≤ n) n

/-- Input bits of the padded sampler: `t = q^{13}` blocks of `2qk` bits, `q = 2^{kOf n}`. -/
abbrev HardIn (n : ℕ) : Type := Fin (2 ^ (13 * kOf n)) × RIn (kOf n)

theorem card_ROut (k : ℕ) (hk : 1 ≤ k) : Fintype.card (ROut k) = 2 ^ (2 * k) + 2 * 2 ^ k * k := by
  have hF : Fintype.card (F k) = 2 ^ k := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card 2 k (by omega)
  simp only [Fintype.card_sum, Fintype.card_prod, hF, Fintype.card_fin, Fintype.card_bool]
  ring

/-- The fixed layout of the first `n₀(k)` output positions as (copy `r < t`, position of `R`). -/
noncomputable def layout (k : ℕ) (hk : 1 ≤ k) : Fin (n₀ k) ≃ Fin (2 ^ (13 * k)) × ROut k :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (Equiv.refl _) (Fintype.equivFinOfCardEq (card_ROut k hk)).symm)

/-- **The DNF sampler of Theorem 4's distribution `D` on `n` bits.** Riazanov–Viola, *Sampling
Tools and the Power of AC0*, STOC 2027 submission (manuscript sha256 99c33d30…), §3, p.8: "Given
Theorem 10 it is trivial to derive Theorem 4: take t := q^{13} independent copies of R and apply
Theorem 1."

With `k = kOf n` and `q = 2^k`: output position `j < n₀(k)`, read through `layout` as (copy `r`,
position `p` of `R`), is the DNF `blockSampler enc k p` of `R` with its variables moved to the
`r`-th block of input bits; the positions `j ≥ n₀(k)` (and all positions when `n < n₀(1)`) get the
empty DNF, i.e. the constant `0`.

**Formalization Note.** The padding to arbitrary `n` and the output layout (a fixed bijection
`Fintype.equivFinOfCardEq`) are this formalization's choices; forests are closed under permuting
and dropping outputs. -/
noncomputable def hardSampler (enc : Encoding) (n : ℕ) : Fin n → DNF (HardIn n) := fun j =>
  if h : (j : ℕ) < n₀ (kOf n) ∧ 1 ≤ kOf n then
    let p := layout (kOf n) h.2 ⟨j, h.1⟩
    (blockSampler enc (kOf n) p.2).rename (fun v => (p.1, v))
  else []

end SamplingAC0


