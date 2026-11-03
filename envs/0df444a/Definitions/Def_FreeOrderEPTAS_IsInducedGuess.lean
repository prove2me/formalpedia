-- Prove2me | Definitions.Def_FreeOrderEPTAS_IsInducedGuess
-- name    : FreeOrderEPTAS_IsInducedGuess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:06.3282+00:00
-- url     : https://prove2.me/theorems/0376861c-1cf8-4bc4-b104-2faf6b1c63a7
-- title:
--   The guesses induced by $x^{(\mathrm{IP})}$
-- statement:
--   For a matrix $x^{(\mathrm{IP})}$ write $N^{(\mathrm{IP})}_{it}=\sum_{j\in J_t}x^{(\mathrm{IP})}_{ij}$ and $S^{(\mathrm{IP})}_{idt}=\sum_{j\in J_t}\ell_{ijd}x^{(\mathrm{IP})}_{ij}$. The guesses it induces are:
--
--   1. if $N^{(\mathrm{IP})}_{it}\le2/\delta$ then $N^\downarrow_{it}=N^\uparrow_{it}=N^{(\mathrm{IP})}_{it}$;
--   2. if $N^{(\mathrm{IP})}_{it}>2/\delta$ then $N^\downarrow_{it}=1/\delta$ and $N^\uparrow_{it}\in[(1-\xi)N^{(\mathrm{IP})}_{it},N^{(\mathrm{IP})}_{it}]$;
--   3. on $d\in A_i$ with $\mathcal T^{(t)}_{id}=0$, $S^\downarrow_{idt}=\lfloor\min\{S^{(\mathrm{IP})}_{idt},1\}\rfloor_{\epsilon/T}$, the largest multiple of $\epsilon/T$ below $\min\{S^{(\mathrm{IP})}_{idt},1\}$.
--
--   `yhat` is the vector $\hat y$ of p.14: $\hat y_{(i,t),j}=x^{(\mathrm{IP})}_{ij}$ if $N^{(\mathrm{IP})}_{it}\le2/\delta$, and $(1-\xi)x^{(\mathrm{IP})}_{ij}$ otherwise.
--
--   **Formalization Note** The paper guesses $\lfloor S^{(\mathrm{IP})}_{idt}\rfloor_{\epsilon/T}$, which takes on the order of $n$ values: $n$ jobs of load $\delta$ in one class, all on machine $i$. That gives $n^{\Theta(\#\text{small triples})}$ guesses, a PTAS count. The cap restores a count depending only on $(\epsilon,m,D)$.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §2.3, p.10; ŷ, p.14

import Mathlib
import Definitions.Def_FreeOrderEPTAS_IPFeasible
import Definitions.Def_FreeOrderEPTAS_typeList

namespace FreeOrderEPTAS

variable {m D n : ℕ}

/-- `N^(IP)_it = ∑_{j ∈ J_t} x^(IP)_ij` (arXiv:2007.13121v3, p.10). -/
noncomputable def Nip (I : SCInstance m D n) (ϵ δ : ℝ) (x : Assignment m n) (i : Fin m)
    (t : Fin (numTypes I ϵ δ)) : ℕ :=
  (Finset.univ.filter fun j => rho I ϵ δ j = t ∧ x i j = true).card

/-- `S^(IP)_idt = ∑_{j ∈ J_t} ℓ_ijd x^(IP)_ij` (p.10). -/
noncomputable def Sip (I : SCInstance m D n) (ϵ δ : ℝ) (x : Assignment m n) (i : Fin m)
    (d : Fin D) (t : Fin (numTypes I ϵ δ)) : ℝ :=
  ∑ j with rho I ϵ δ j = t, I.ℓ i j d * bit (x i j)

/-- The guesses of §2.3 (p.10) induced by `x^(IP)`, with the correction of the small-load guess:
- if `N^(IP)_it ≤ 2/δ` then `N↓_it = N↑_it = N^(IP)_it`;
- if `N^(IP)_it > 2/δ` then `N↓_it = 1/δ` and `N↑_it ∈ [(1 - ξ) N^(IP)_it, N^(IP)_it]`;
- on `d ∈ A_i`, `T^(t)_id = 0`, `S↓_idt = ⌊min{S^(IP)_idt, 1}⌋_{ϵ/T}`, the multiple of `ϵ/T` below
  `min{S^(IP)_idt, 1}`.

**Formalization Note.** The paper guesses `⌊S^(IP)_idt⌋_{ϵ/T}`, which takes up to order `n` values;
the cap keeps the number of guesses a function of `(ϵ, m, D)`. -/
structure IsInducedGuess (I : SCInstance m D n) (ϵ δ ξ : ℝ) (x : Assignment m n)
    (Nlo Nhi : Fin m → Fin (numTypes I ϵ δ) → ℕ)
    (Slo : Fin m → Fin D → Fin (numTypes I ϵ δ) → ℝ) : Prop where
  /-- The case `N^(IP)_it ≤ 2/δ`. -/
  exact : ∀ i t, (Nip I ϵ δ x i t : ℝ) ≤ 2 / δ →
    Nlo i t = Nip I ϵ δ x i t ∧ Nhi i t = Nip I ϵ δ x i t
  /-- The case `N^(IP)_it > 2/δ`. -/
  approx : ∀ i t, 2 / δ < (Nip I ϵ δ x i t : ℝ) →
    (Nlo i t : ℝ) = 1 / δ ∧ (1 - ξ) * (Nip I ϵ δ x i t : ℝ) ≤ (Nhi i t : ℝ) ∧
      (Nhi i t : ℝ) ≤ (Nip I ϵ δ x i t : ℝ)
  /-- The small-load guess. -/
  small : ∀ i, ∀ d ∈ I.A i, ∀ t, typeOf I ϵ δ t i d = 0 →
    Slo i d t = (⌊min (Sip I ϵ δ x i d t) 1 / (ϵ / (numTypes I ϵ δ : ℝ))⌋₊ : ℝ) *
      (ϵ / (numTypes I ϵ δ : ℝ))

/-- The candidate solution `ŷ` of the proof of Lemma 2.2 (p.14): `ŷ_{(i,t),j} = x^(IP)_ij` if
`N^(IP)_it ≤ 2/δ`, and `(1 - ξ) x^(IP)_ij` if `N^(IP)_it > 2/δ`, with `t = ρ(j)`. -/
noncomputable def yhat (I : SCInstance m D n) (ϵ δ ξ : ℝ) (x : Assignment m n) :
    Fin m → Fin n → ℝ :=
  fun i j =>
    (if (Nip I ϵ δ x i (rho I ϵ δ j) : ℝ) ≤ 2 / δ then 1 else (1 - ξ)) * bit (x i j)

end FreeOrderEPTAS


