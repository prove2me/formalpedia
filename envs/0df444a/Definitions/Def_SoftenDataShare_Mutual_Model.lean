-- Prove2me | Definitions.Def_SoftenDataShare_Mutual_Model
-- name    : SoftenDataShare_Mutual_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T23:12:21.487984+00:00
-- url     : https://prove2.me/theorems/67dcb120-14ed-49b1-99fd-1e81c7ad68ca
-- title:
--   Sections 3.1–3.2 — benchmark z^N, prices and profits, and the profits π₂₁, π₂₂, π₁, π₂ under data sharing on [a, b]
-- statement:
--   Consumers are located on $[0,1]$ with distribution $F$ and density $f$ (a monotone-hazard-rate distribution, see the definition `MHRDist`); $h=f/(1-F)$ is the hazard rate. Firm 1 sits at $0$ and knows every consumer's location; firm 2 sits at $1$; transport cost equals distance and production is costless. This file defines the quantities of Sections 3.1 and 3.2.
--
--   **Benchmark without data sharing (Eqs. (1)–(2)).** A number $z$ is the benchmark marginal consumer $z^N$ if
--   $$z\in(1/2,1),\qquad z=\frac12+\frac1{h(z)}.$$
--   Given $z^N$, firm 2's uniform price and the two firms' profits are
--   $$p^N_2=\frac{2}{h(z^N)},\qquad \pi^N_1=\int_0^{z^N}\bigl(p^N_2+(1-2x)\bigr)\,dF(x),\qquad \pi^N_2=p^N_2\,(1-F(z^N)).$$
--
--   **Data sharing on $[a,b]$ (Eqs. (4), (5), (7), (8)).** When firm 1 shares the data of consumers in $[a,b]$ and firm 2's uniform price serves only $[b,1]$, firm 2 charges $p_{21}=2b-1$ and earns
--   $$\pi_{21}(b)=(2b-1)(1-F(b)).$$
--   If instead firm 2's uniform price serves $[z',a]\cup[b,1]$ for some $z'\le a$, it charges $2z'-1$ and earns $(2z'-1)(1-F(b)+F(a)-F(z'))$; the best such profit is
--   $$\pi_{22}(a,b)=\max_{z'\in[0,a]}\,(2z'-1)\bigl(1-F(b)+F(a)-F(z')\bigr).$$
--   When firm 2 prices personally on $[a,b]$ at $2x-1$ and uniformly at $2b-1$ on $[b,1]$, and firm 1 serves $[0,a]$ at the personalized price $p_{21}+(1-2x)$, the profits are
--   $$\pi_2(a,b)=\int_a^b(2x-1)\,dF(x)+\pi_{21}(b),\qquad \pi_1(a,b)=\int_0^a\bigl((2b-1)+(1-2x)\bigr)\,dF(x).$$
--
--   These are the objects compared in Lemma 2 and Proposition 1: firm 2's incentive constraint (IC) is $\pi_{21}(b)\ge\pi_{22}(a,b)$ and its participation constraint (IR) is $\pi_2(a,b)\ge\pi^N_2$.
--
--   **Formalization Note** Every $dF$ integral is the interval integral of the integrand times the density $f$. $z^N$ is not a function of $(F,f)$: theorems take a number `zN` together with the hypothesis `IsZN F f zN`, and a separate theorem shows such a number exists and is unique. $\pi_{22}$ is the supremum of the image of $[0,a]$, which is the maximum when $0\le a\le1$ (continuous function on a compact interval); for $a<0$ the set is empty and the junk value is $0$. Theorems only use $a=z^N$. Firm 1's profit does not involve $F$ except through its density, so `pi1` takes only $f$.
-- source:
--   Choe, Cong & Wang, Softening Competition through Unilateral Sharing of Customer Data, Monash Discussion Paper 2021-10 (rev. Oct. 20, 2022), pp. 8–11, Section 3.1, Eqs. (1)–(2), and Section 3.2, Eqs. (4), (5), (7), (8)

import Mathlib
import Definitions.Def_SoftenDataShare_Mutual_MHRDist

namespace SoftenDataShare.Mutual

/-- `z` is the benchmark marginal consumer `z^N` of Eq. (1): `z ∈ (1/2, 1)` and
`z = 1/2 + 1 / h(z)`. -/
def IsZN (F f : ℝ → ℝ) (z : ℝ) : Prop :=
  z ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧ z = 1 / 2 + 1 / hazard F f z

/-- Firm 2's benchmark uniform price `p^N_2 = 2 / h(z^N)` (Eq. (1)), as a function of `z^N`. -/
noncomputable def pN2 (F f : ℝ → ℝ) (zN : ℝ) : ℝ := 2 / hazard F f zN

/-- Firm 1's benchmark profit `π^N_1 = ∫_0^{z^N} (p^N_2 + (1 - 2x)) dF(x)` (Eq. (2)). -/
noncomputable def piN1 (F f : ℝ → ℝ) (zN : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..zN, (pN2 F f zN + (1 - 2 * x)) * f x

/-- Firm 2's benchmark profit `π^N_2 = p^N_2 (1 - F(z^N))` (Eq. (2)). -/
noncomputable def piN2 (F f : ℝ → ℝ) (zN : ℝ) : ℝ := pN2 F f zN * (1 - F zN)

/-- Firm 2's profit when its uniform price `p21 = 2b - 1` serves only `[b, 1]`:
`π21(b) = (2b - 1)(1 - F(b))` (Eq. (4)). -/
def pi21 (F : ℝ → ℝ) (b : ℝ) : ℝ := (2 * b - 1) * (1 - F b)

/-- Firm 2's maximal profit when its uniform price serves `[z', a] ∪ [b, 1]` for some `z' ≤ a`:
`π22(a, b) = max_{z' ∈ [0, a]} (2z' - 1)(1 - F(b) + F(a) - F(z'))` (p. 10, before Eq. (5)).
On `a < 0` the set is empty and Lean's `sSup ∅ = 0` is a junk value; the mission only uses
`a = z^N ∈ (1/2, 1)`. -/
noncomputable def pi22 (F : ℝ → ℝ) (a b : ℝ) : ℝ :=
  sSup ((fun z => (2 * z - 1) * (1 - F b + F a - F z)) '' Set.Icc 0 a)

/-- Firm 2's profit under data sharing on `[a, b]` when its uniform price is `p21 = 2b - 1`:
`π2(a, b) = ∫_a^b (2x - 1) dF(x) + π21(b)` (Eq. (7)). -/
noncomputable def pi2 (F f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (∫ x in a..b, (2 * x - 1) * f x) + pi21 F b

/-- Firm 1's profit under data sharing on `[a, b]` when firm 2's uniform price is `p21 = 2b - 1`:
`π1(a, b) = ∫_0^a (p21 + (1 - 2x)) dF(x)` (Eq. (8)). -/
noncomputable def pi1 (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..a, ((2 * b - 1) + (1 - 2 * x)) * f x

end SoftenDataShare.Mutual


