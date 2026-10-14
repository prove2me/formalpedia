-- Prove2me | Definitions.Def_IwasawaMainConjecture_analytic
-- name    : IwasawaMainConjecture_analytic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T17:22:31.541985+00:00
-- url     : https://prove2.me/theorems/4144c652-08fd-4c06-9ff0-679f3fb1b0e8
-- title:
--   Teichmüller character, generalized Bernoulli numbers $B_{k,\omega^j}$ and the Iwasawa power series $G_p(\omega^j,T)$
-- statement:
--   This file sets up the analytic side of the main conjecture of Iwasawa theory for a prime $p$.
--
--   1. `teichmuller p a` is the Teichmüller representative $\omega(a) \in \mathbb{Z}_p$ of $a \in \mathbb{Z}/p$: the unique $c \in \mathbb{Z}_p$ with $c^p = c$ and $c \equiv a \pmod p$.
--   2. `omegaPow p j` is the Dirichlet character $\omega^j$ modulo $p$ with values in $\mathbb{Z}_p$. It vanishes on multiples of $p$; for $j \equiv 0 \pmod{p-1}$ it is the principal character modulo $p$.
--   3. `genBernoulli p j k` is the generalized Bernoulli number
--   $$B_{k,\omega^j} = p^{k-1} \sum_{a=1}^{p} \omega^j(a)\, B_k\!\left(\tfrac{a}{p}\right) \in \mathbb{Q}_p,$$
--   where $B_k(X)$ is the $k$-th Bernoulli polynomial.
--   4. `IsTopologicalGenerator p u` says that $u \in \mathbb{Z}_p^\times$ topologically generates $1 + p\mathbb{Z}_p$: the closure of $\{u^n : n \in \mathbb{Z}\}$ is $\{x \in \mathbb{Z}_p : x \equiv 1 \pmod p\}$.
--   5. `IsIwasawaPowerSeries p u j G` says that $G = \sum_n a_n T^n \in \mathbb{Z}_p[[T]]$ is the power series $G_p(\omega^j, T)$, i.e. $G_p(\omega^j, u^s - 1) = L_p(\omega^j, s)$, where the Kubota–Leopoldt $p$-adic $L$-function is characterised by $L_p(\omega^j, 1-k) = -B_{k,\omega^{j-k}}/k$. Concretely, for every integer $k \ge 1$,
--   $$\sum_{n \ge 0} a_n \,(u^{1-k} - 1)^n = -\frac{B_{k,\omega^{j-k}}}{k}.$$
--
--   These are the objects $\omega$, $B_k(\chi)$, $L_p$, $u$ and $G_p$ of the source's statement.
--
--   **Formalization Note** The Teichmüller representative is chosen with `Classical.epsilon`; it is unique by Hensel's lemma. The characters $\omega^{j}$ are always taken modulo $p$, also when $\omega^{j}$ is trivial. With this convention the formula $B_{k,\chi} = p^{k-1}\sum_{a=1}^{p}\chi(a)B_k(a/p)$ automatically contains the Euler factor $1 - p^{k-1}$, so the source's interpolation formula is the correct one for every $k \ge 1$. The infinite sum is the topological sum `tsum` in $\mathbb{Q}_p$; it converges because $|u^{1-k}-1|_p < 1$.
-- source:
--   Wikipedia, "Main conjecture of Iwasawa theory", revision oldid=1367440598, https://en.wikipedia.org/w/index.php?title=Main_conjecture_of_Iwasawa_theory&oldid=1367440598, section "Statement" (ω, L_p(ω^i,1−k) = −B_k(ω^{i−k})/k, u, G_p(ω^i,u^s−1) = L_p(ω^i,s)); Iwasawa 1969, https://doi.org/10.2307/1970817

import Mathlib

/-!
# Iwasawa main conjecture — analytic side

Teichmüller character, generalized Bernoulli numbers, and the Iwasawa power series
`G_p(ω^j, T)` characterised by interpolating the Kubota–Leopoldt `p`-adic `L`-function
`L_p(ω^j, s)` at `s = 1 - k`.
-/

open scoped Polynomial

namespace IwasawaMainConjecture

variable (p : ℕ) [Fact p.Prime]

/-- The Teichmüller representative `ω(a) ∈ ℤ_p` of `a ∈ ℤ/p`: the unique `c ∈ ℤ_p` with
`c ^ p = c` and `c ≡ a (mod p)` (so `ω(0) = 0`, and `ω(a)` is a `(p-1)`-st root of unity
for `a ≠ 0`). -/
noncomputable def teichmuller (a : ZMod p) : ℤ_[p] :=
  Classical.epsilon fun c : ℤ_[p] => c ^ p = c ∧ PadicInt.toZMod c = a

open Classical in
/-- The Dirichlet character `ω^j` modulo `p` with values in `ℤ_p`, where `ω` is the
Teichmüller character; it vanishes on multiples of `p` (also for `ω^0`, which is the
principal character modulo `p`). -/
noncomputable def omegaPow (j : ℤ) (a : ZMod p) : ℤ_[p] :=
  if a = 0 then 0 else teichmuller p a ^ (j % ((p : ℤ) - 1)).toNat

/-- The generalized Bernoulli number `B_{k, ω^j} = p^{k-1} ∑_{a=1}^{p} ω^j(a) B_k(a/p) ∈ ℚ_p`
of the character `ω^j` regarded as a character modulo `p`, where `B_k(X)` is the `k`-th
Bernoulli polynomial. -/
noncomputable def genBernoulli (j : ℤ) (k : ℕ) : ℚ_[p] :=
  (p : ℚ_[p]) ^ (k - 1) * ∑ a ∈ Finset.range p,
    (omegaPow p j (a : ZMod p) : ℚ_[p]) *
      (((Polynomial.bernoulli k).eval ((a : ℚ) / p) : ℚ) : ℚ_[p])

/-- `u ∈ ℤ_p^×` is a topological generator of the multiplicative group `1 + pℤ_p`:
the closure of `{u^n : n ∈ ℤ}` is exactly `{x ∈ ℤ_p : x ≡ 1 (mod p)}`. -/
def IsTopologicalGenerator (u : ℤ_[p]ˣ) : Prop :=
  closure (Set.range fun n : ℤ => ((u ^ n : ℤ_[p]ˣ) : ℤ_[p])) =
    {x : ℤ_[p] | PadicInt.toZMod x = 1}

/-- `G ∈ ℤ_p[[T]]` is the Iwasawa power series `G_p(ω^j, T)` attached to `u`:
`G(u^s - 1) = L_p(ω^j, s)`, where the Kubota–Leopoldt `p`-adic `L`-function is characterised
by `L_p(ω^j, 1 - k) = - B_{k, ω^{j-k}} / k` for all integers `k ≥ 1`. Concretely,
`∑ₙ aₙ (u^{1-k} - 1)^n = - B_{k, ω^{j-k}} / k` for every `k ≥ 1`. -/
def IsIwasawaPowerSeries (u : ℤ_[p]ˣ) (j : ℤ) (G : PowerSeries ℤ_[p]) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∑' n : ℕ, ((PowerSeries.coeff n G : ℤ_[p]) : ℚ_[p]) *
        ((((u ^ (1 - (k : ℤ)) : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) - 1) ^ n =
      - genBernoulli p (j - k) k / k

end IwasawaMainConjecture


