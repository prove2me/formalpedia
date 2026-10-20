-- Prove2me | Definitions.Def_IPLicense3D_Pooling_Model
-- name    : IPLicense3D_Pooling_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:51.70024+00:00
-- url     : https://prove2.me/theorems/1a1e1e6e-ff29-46f1-be8c-b5aaffa3eacb
-- title:
--   §3, (3)–(11), pp. 2690–2692 — buyer costs, surplus, channel selection, OEM profit and efficacy under an IP license (f, r)
-- statement:
--   This file sets up the model of Zhang, Westerweel, Basten and Song (2022). An original equipment manufacturer (OEM) supplies one spare part to $n$ buyers $i \in \mathcal N = \{1,\dots,n\}$. Buyer $i$ faces Poisson demand at annual rate $\lambda_i > 0$. All buyers share the holding-cost rate $h$ (per unit value per year) and the safety factor $z$ of their reorder point. The OEM sells at wholesale price $w$ and produces at unit cost $c$.
--
--   **Traditional channel.** A buyer orders from the OEM with fixed ordering cost $k_T$ and lead time $\ell_T$. Its expected annual cost is (3):
--   $$
--   C_{T,i} = hw\left(\lambda_i\ell_T + z\sqrt{\lambda_i\ell_T}\right) + \sqrt{2hw\lambda_i k_T} + w\lambda_i .
--   $$
--
--   **Licensing channel.** Under an IP license $(f, r)$ — a fixed annual fee $f$ and a royalty $r$ per printed part — the buyer 3D prints locally at printing price $p$, with fixed ordering cost $k_A$ and lead time $\ell_A$. Its expected annual cost is (5):
--   $$
--   C_{A,i}(f,r) = f + h(r+p)\left(\lambda_i\ell_A + z\sqrt{\lambda_i\ell_A}\right) + \sqrt{2h(r+p)\lambda_i k_A} + (r+p)\lambda_i .
--   $$
--
--   **Surplus and channel selection.** Buyer $i$'s surplus is $S_i(f,r) = C_{T,i} - C_{A,i}(f,r)$ (7), and its maximum surplus is $\bar S_i = S_i(0,0)$ (10). A buyer takes the license if it is not worse off, so the set of licensees is $\mathcal N_A(f,r) = \{i \in \mathcal N \mid S_i(f,r) \ge 0\}$ and the rest, $\mathcal N_T(f,r) = \mathcal N \setminus \mathcal N_A(f,r)$, stay traditional.
--
--   **Profits.** The OEM earns $\Pi_{T,i} = (w-c)\lambda_i$ from a traditional buyer and $\Pi_{A,i}(f,r) = f + r\lambda_i$ (6) from a licensee. Its total profit is (8)
--   $$
--   \Pi(f,r) = \sum_{i \in \mathcal N_T(f,r)} \Pi_{T,i} + \sum_{i \in \mathcal N_A(f,r)} \Pi_{A,i}(f,r),
--   $$
--   and its problem (9) is to maximize $\Pi$ over valid licenses $f \ge 0$, $r \ge 0$. The file records the set $\{\Pi(f,r) \mid f \ge 0,\ r \ge 0\}$ of attainable profits.
--
--   **Efficacy.** With $S_{\max} = \sum_{i \in \mathcal N_A(0,0)} \bar S_i$, the efficacy of a license is (11) $\eta(f,r) = \sum_{i \in \mathcal N_A(f,r)} \Pi_{A,i}(f,r) / S_{\max}$.
--
--   **Standing assumptions.** $h, w, p, k_A, \ell_A > 0$, $k_A < k_T$, $\ell_A < \ell_T$ (p. 2690), $\lambda_i > 0$ for all $i$, and $z \ge 0$. The unit cost $c$ has no sign restriction.
--
--   **Table 1 values.** For two buyers, the file also names the largest entry of the profit column of each case of Table 1 (p. 2695). Case I takes the maximum of $(w-c)\lambda_1 + \bar S_2$, $2\bar S_1$, $2S_1(0,\hat r) + \hat r(\lambda_1+\lambda_2)$, $(w-c)\lambda_2 + S_1(0,\hat r) + \hat r\lambda_1$ and $(w-c)(\lambda_1+\lambda_2)$. Case II takes the maximum of $(w-c)\lambda_1 + \bar S_2$, $2\bar S_1$, $\bar r_1(0)(\lambda_1+\lambda_2)$ and $(w-c)(\lambda_1+\lambda_2)$. Case III takes the maximum of $2\bar S_2$, $(w-c)\lambda_2 + \bar S_1$ and $(w-c)(\lambda_1+\lambda_2)$.
--
--   These definitions are the common ground of every statement in the mission.
--
--   **Formalization Note** Buyers are `Fin n`; for two buyers the paper's Buyer 1 is index `0` and Buyer 2 is index `1`. The costs (3) and (5) are taken as definitions: the paper derives them from an $(R,Q)$ policy with a normal approximation of lead-time demand (Online Appendix B), and that derivation is not formalized. The paper prints "$z = \Phi(\beta)$" (p. 2690); it means $z = \Phi^{-1}(\beta)$, and $z \ge 0$ (service level $\beta \ge 1/2$) is added because Lemma 1(iv) and Corollary 2 fail for sufficiently negative $z$. The cost functions are also available with every parameter explicit (`costTF`, `costAF`, `surplusF`), so that derivatives in $\lambda$, $w$ and $p$ can be stated. `withW w'` is the same model with wholesale price $w'$. The efficacy is meaningful only when $S_{\max} > 0$ (Lean's division returns $0$ otherwise).
-- source:
--   Zhang, Westerweel, Basten & Song, Distributed 3D Printing of Spare Parts via IP Licensing, MSOM 24(5) 2022, pp. 2690–2692, §3 (3), (5)–(9), §4.1 (10), §4.2 (11); p. 2695, Table 1

import Mathlib

namespace IPLicense3D.Pooling

/-- Buyer's expected annual cost in the traditional channel, (3), p. 2690:
`C_T = h w (λ ℓ_T + z √(λ ℓ_T)) + √(2 h w λ k_T) + w λ`. -/
noncomputable def costTF (h w kT ellT z lam : ℝ) : ℝ :=
  h * w * (lam * ellT + z * Real.sqrt (lam * ellT)) + Real.sqrt (2 * h * w * lam * kT) + w * lam

/-- Buyer's expected annual cost under the IP license `(f, r)`, (5), p. 2691:
`C_A(f, r) = f + h (r + p) (λ ℓ_A + z √(λ ℓ_A)) + √(2 h (r + p) λ k_A) + (r + p) λ`. -/
noncomputable def costAF (h p kA ellA z lam f r : ℝ) : ℝ :=
  f + h * (r + p) * (lam * ellA + z * Real.sqrt (lam * ellA))
    + Real.sqrt (2 * h * (r + p) * lam * kA) + (r + p) * lam

/-- Buyer's surplus, (7), p. 2691: `S(f, r) = C_T − C_A(f, r)`, as a function of all parameters. -/
noncomputable def surplusF (h w p kT kA ellT ellA z lam f r : ℝ) : ℝ :=
  costTF h w kT ellT z lam - costAF h p kA ellA z lam f r

/-- The model of §3 with `n` buyers indexed by `Fin n`: holding-cost rate `h`, wholesale price `w`,
unit production cost `c`, printing price `p`, fixed ordering costs `kT`, `kA`, lead times `ellT`, `ellA`,
safety factor `z`, and demand rates `lam i`. -/
structure Model (n : ℕ) where
  h : ℝ
  w : ℝ
  c : ℝ
  p : ℝ
  kT : ℝ
  kA : ℝ
  ellT : ℝ
  ellA : ℝ
  z : ℝ
  lam : Fin n → ℝ

namespace Model

variable {n : ℕ} (M : Model n)

/-- Standing assumptions: positive parameters, `k_A < k_T`, `ℓ_A < ℓ_T` (p. 2690), positive demand
rates, and `z ≥ 0` (added: `z = Φ⁻¹(β)` with service level `β ≥ 1/2`). -/
def Standing : Prop :=
  0 < M.h ∧ 0 < M.w ∧ 0 < M.p ∧ 0 < M.kA ∧ M.kA < M.kT ∧ 0 < M.ellA ∧ M.ellA < M.ellT ∧
    0 ≤ M.z ∧ ∀ i, 0 < M.lam i

/-- Buyer `i`'s traditional cost `C_{T,i}`, (3). -/
noncomputable def costT (i : Fin n) : ℝ := costTF M.h M.w M.kT M.ellT M.z (M.lam i)

/-- Buyer `i`'s licensed cost `C_{A,i}(f, r)`, (5). -/
noncomputable def costA (i : Fin n) (f r : ℝ) : ℝ := costAF M.h M.p M.kA M.ellA M.z (M.lam i) f r

/-- The surplus of a buyer with demand rate `l` under the license `(f, r)`, (7). -/
noncomputable def surplusL (l f r : ℝ) : ℝ :=
  surplusF M.h M.w M.p M.kT M.kA M.ellT M.ellA M.z l f r

/-- Buyer `i`'s surplus `S_i(f, r) = C_{T,i} − C_{A,i}(f, r)`, (7). -/
noncomputable def surplus (i : Fin n) (f r : ℝ) : ℝ := M.surplusL (M.lam i) f r

/-- Buyer `i`'s maximum surplus `S̄_i = S_i(0, 0)`, (10). -/
noncomputable def maxSurplus (i : Fin n) : ℝ := M.surplus i 0 0

/-- The buyers who opt for IP licensing, `N_A(f, r) = {i | S_i(f, r) ≥ 0}` (§3.3; ties go to the
license). -/
noncomputable def optsIn (f r : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 0 ≤ M.surplus i f r)

/-- The OEM's profit from buyer `i` in the traditional channel, `Π_{T,i} = (w − c) λ_i` (p. 2690). -/
def profitT (i : Fin n) : ℝ := (M.w - M.c) * M.lam i

/-- The OEM's profit from buyer `i` in the licensing channel, `Π_{A,i}(f, r) = f + r λ_i`, (6). -/
def profitA (i : Fin n) (f r : ℝ) : ℝ := f + r * M.lam i

/-- The OEM's total profit (8): `Π(f, r) = Σ_{i ∈ N_T(f,r)} Π_{T,i} + Σ_{i ∈ N_A(f,r)} Π_{A,i}(f, r)`,
with `N_T(f, r) = N ∖ N_A(f, r)`. -/
noncomputable def oemProfit (f r : ℝ) : ℝ :=
  (∑ i ∈ Finset.univ \ M.optsIn f r, M.profitT i) + ∑ i ∈ M.optsIn f r, M.profitA i f r

/-- The profits of all valid licenses, `{Π(f, r) | f ≥ 0, r ≥ 0}`; the OEM's problem (9) is the
maximization over this set. -/
def validProfits : Set ℝ := {v | ∃ f r : ℝ, 0 ≤ f ∧ 0 ≤ r ∧ M.oemProfit f r = v}

/-- The maximum total surplus `S_max = Σ_{i ∈ N_A(0,0)} S̄_i` (p. 2692). -/
noncomputable def maxTotalSurplus : ℝ := ∑ i ∈ M.optsIn 0 0, M.maxSurplus i

/-- The efficacy (11) of the license `(f, r)`: `η(f, r) = Σ_{i ∈ N_A(f,r)} Π_{A,i}(f, r) / S_max`
(meaningful when `S_max > 0`). -/
noncomputable def efficacy (f r : ℝ) : ℝ :=
  (∑ i ∈ M.optsIn f r, M.profitA i f r) / M.maxTotalSurplus

/-- The same model with the wholesale price replaced by `w'`. -/
def withW (w' : ℝ) : Model n := { M with w := w' }

/-- Table 1, Case I (p. 2695): the largest of the five listed profits, with buyer 1 = index `0`,
buyer 2 = index `1`, and `rh` the royalty fee `r̂`. -/
noncomputable def caseIValue (M : Model 2) (rh : ℝ) : ℝ :=
  max ((M.w - M.c) * M.lam 0 + M.maxSurplus 1)
    (max (2 * M.maxSurplus 0)
      (max (2 * M.surplus 0 0 rh + rh * (M.lam 0 + M.lam 1))
        (max ((M.w - M.c) * M.lam 1 + M.surplus 0 0 rh + rh * M.lam 0)
          ((M.w - M.c) * (M.lam 0 + M.lam 1)))))

/-- Table 1, Case II (p. 2695): the largest of the four listed profits, with `rb0 = r̄_1(0)`. -/
noncomputable def caseIIValue (M : Model 2) (rb0 : ℝ) : ℝ :=
  max ((M.w - M.c) * M.lam 0 + M.maxSurplus 1)
    (max (2 * M.maxSurplus 0)
      (max (rb0 * (M.lam 0 + M.lam 1))
        ((M.w - M.c) * (M.lam 0 + M.lam 1))))

/-- Table 1, Case III (p. 2695): the largest of the three listed profits. -/
noncomputable def caseIIIValue (M : Model 2) : ℝ :=
  max (2 * M.maxSurplus 1)
    (max ((M.w - M.c) * M.lam 1 + M.maxSurplus 0)
      ((M.w - M.c) * (M.lam 0 + M.lam 1)))

end Model

end IPLicense3D.Pooling


