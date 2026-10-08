-- Prove2me | Definitions.Def_MulticlassQNet_FirstOrder_Constraints
-- name    : MulticlassQNet_FirstOrder_Constraints
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:10:16.784869+00:00
-- url     : https://prove2.me/theorems/245ef9d9-e641-4197-a0cf-9008a2375eaa
-- title:
--   §4 — restriction (17) on the f-parameters, N'(S) and D'(S) of (18), and the equalities (24), (25), (28)
-- statement:
--   These are the deterministic expressions of §4, written for a network with traffic rates $\lambda$. Throughout, a sum "$r'\notin S$" includes the exit $r'=0$, as the paper states on p. 15.
--
--   **Restriction (17).** For a set $S$ of classes, real f-parameters $f(r)$ and station values $f_i$, require for every $r\in S$
--   $$\mu_r\Big[\sum_{r'\in S}p_{rr'}\big(f(r)-f(r')\big)+\sum_{r'\notin S}p_{rr'}f(r)\Big]=f_{\sigma(r)},$$
--   with $f_i\ge0$ for every station and $f_i=0$ when $C_i\cap S=\emptyset$. Equivalently, the bracketed expression is nonnegative and the same for all $r\in C_i\cap S$, and $f_i$ is its common value.
--
--   **The bound (18).**
--   $$N'(S)=\sum_{r\in S}\lambda_{0r}f^2(r)+\sum_{r\notin S}\lambda_r\sum_{r'\in S}p_{rr'}f^2(r')+\sum_{r\in S}\lambda_r\Big[\sum_{r'\in S}p_{rr'}\big(f(r)-f(r')\big)^2+\sum_{r'\notin S}p_{rr'}f^2(r)\Big],$$
--   $$D'(S)=2\Big[\sum_{i=1}^Nf_i-\sum_{r\in S}\lambda_{0r}f(r)\Big].$$
--   In $N'(S)$ the outer sum over $r\notin S$ ranges over classes only; the exit convention applies to the inner sums over $r'$.
--
--   **The equalities of Theorems 4.2 and 4.3**, in real variables $n_r$ (standing for $\lambda_rx_r$), $I_{rr'}$ and $N_{ir'}$:
--   $$2\mu_rI_{rr}-2\sum_{r'=1}^R\mu_{r'}p_{r'r}I_{r'r}-2\lambda_{0r}n_r=\lambda_{0r}+\lambda_r(1-p_{rr})+\sum_{r'\ne r}\lambda_{r'}p_{r'r}\quad(24)$$
--   for every $r$;
--   $$\mu_rI_{rr'}+\mu_{r'}I_{r'r}-\sum_{w=1}^R\mu_wp_{wr}I_{wr'}-\sum_{w=1}^R\mu_wp_{wr'}I_{wr}-\lambda_{0r}n_{r'}-\lambda_{0r'}n_r=-\lambda_rp_{rr'}-\lambda_{r'}p_{r'r}\quad(25)$$
--   for all $r>r'$; and
--   $$\sum_{r\in C_i}I_{rr'}+N_{ir'}=n_{r'}\quad(28)$$
--   for every station $i$ and class $r'$.
--
--   Theorem 4.1 and Theorem 4.4 share (17), $N'$ and $D'$; Theorems 4.2, 4.3 and 4.4 share (24), (25), (28). Little's law identifies the stochastic mean numbers in Theorem 4.1 with the products $\lambda_rx_r$ in Theorem 4.4.
--
--   **Formalization Note** The exit term enters as `exitProb r` added to the sum over `Sᶜ`. The sum in (24) over $r'$ includes $r'=r$. In (25) "$r>r'$" is the order on `Fin R`. The variable written $\lambda_rx_r$ in the paper is a single real `n r`.
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), p. 14, Eqs. (17)–(18); p. 15 (exit convention); p. 18, Eqs. (24)–(25); p. 20, Eq. (28)

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network

namespace MulticlassQNet.FirstOrder

namespace Network

variable {N R : ℕ} (net : Network N R)

/-- Restriction (17) on the f-parameters `f` for the class set `S`, with station values `fi`:
for every `r ∈ S`, `μ_r [∑_{r'∈S} p_{rr'}(f(r) - f(r')) + ∑_{r'∉S} p_{rr'} f(r)] = f_{σ(r)}`,
where the sum over `r' ∉ S` includes the exit `r' = 0`; every `f_i ≥ 0`; and `f_i = 0` when
`C_i ∩ S = ∅`. -/
def FCondition (S : Finset (Fin R)) (f : Fin R → ℝ) (fi : Fin N → ℝ) : Prop :=
  (∀ r ∈ S, net.μ r * (∑ r' ∈ S, net.p r r' * (f r - f r') +
      (∑ r' ∈ Sᶜ, net.p r r' + net.exitProb r) * f r) = fi (net.σ r)) ∧
  (∀ i, 0 ≤ fi i) ∧
  (∀ i, (∀ r ∈ S, net.σ r ≠ i) → fi i = 0)

/-- The numerator `N'(S)` of (18); the sums over `r' ∉ S` include the exit `r' = 0`. -/
def Nprime (lam : Fin R → ℝ) (S : Finset (Fin R)) (f : Fin R → ℝ) : ℝ :=
  ∑ r ∈ S, net.lam0 r * f r ^ 2 +
  ∑ r ∈ Sᶜ, lam r * ∑ r' ∈ S, net.p r r' * f r' ^ 2 +
  ∑ r ∈ S, lam r * (∑ r' ∈ S, net.p r r' * (f r - f r') ^ 2 +
      (∑ r' ∈ Sᶜ, net.p r r' + net.exitProb r) * f r ^ 2)

/-- The denominator `D'(S) = 2 [∑_{i=1}^N f_i - ∑_{r∈S} λ_{0r} f(r)]` of (18). -/
def Dprime (S : Finset (Fin R)) (f : Fin R → ℝ) (fi : Fin N → ℝ) : ℝ :=
  2 * (∑ i, fi i - ∑ r ∈ S, net.lam0 r * f r)

/-- Equalities (24) of Theorem 4.2, in the variables `n r` (for `λ_r x_r`) and `I r r'`. -/
def Eq24 (lam n : Fin R → ℝ) (I : Fin R → Fin R → ℝ) : Prop :=
  ∀ r, 2 * net.μ r * I r r - 2 * ∑ r', net.μ r' * net.p r' r * I r' r
      - 2 * net.lam0 r * n r
    = net.lam0 r + lam r * (1 - net.p r r) + ∑ r' ∈ Finset.univ.erase r, lam r' * net.p r' r

/-- Equalities (25) of Theorem 4.2, for all classes `r' < r`. -/
def Eq25 (lam n : Fin R → ℝ) (I : Fin R → Fin R → ℝ) : Prop :=
  ∀ r r', r' < r →
    net.μ r * I r r' + net.μ r' * I r' r - ∑ w, net.μ w * net.p w r * I w r'
      - ∑ w, net.μ w * net.p w r' * I w r - net.lam0 r * n r' - net.lam0 r' * n r
    = -(lam r * net.p r r') - lam r' * net.p r' r

/-- Equalities (28) of Theorem 4.3, in the variables `n`, `I` and `Nv i r'` (for `N_{ir'}`). -/
def Eq28 (n : Fin R → ℝ) (I : Fin R → Fin R → ℝ) (Nv : Fin N → Fin R → ℝ) : Prop :=
  ∀ i r', ∑ r ∈ net.C i, I r r' + Nv i r' = n r'

end Network

end MulticlassQNet.FirstOrder


