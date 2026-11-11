-- Prove2me | Definitions.Def_LeakageRefresh_Continual_OneRound
-- name    : LeakageRefresh_Continual_OneRound
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:10:22.006891+00:00
-- url     : https://prove2.me/theorems/0e6ed343-6865-46e6-9276-9b4ebae2648e
-- title:
--   One refresh: leakage probability tables $\mathrm{prob}_{i,h,z}$, consistency projection, sign table $J$, residual $\Delta_z$, $F^M$, $\mathrm{disc}_n$, local-approximation conditions (4.58)–(4.64)
-- statement:
--   Fix a pair of leakage functions (selected by a round $i$, a formal incoming history $h$ and the adversary's tape) and an answer $z$. For states $x=(\ell,r)$, $x'=(\ell',r')$ the **leakage probability function** is
--   $$\mathrm{prob}_{i,h,z}(x,x')=\Pr_{M\leftarrow\mathrm{InvMatr}^n_2}\big[Z_i=z\ \big|\ \ell\cdot M=\ell',\ M^{-1}\cdot r=r'\big].$$
--   A **four-share tuple** is $\omega=((\ell,\ell'),(r,r'))\in U_L^2\times U_R^2$, with rows $(\ell,\ell')$ and columns $(r,r')$; it is **consistent** when $\ell'\cdot r'=\ell\cdot r$. The table $\mathrm{prob}_z(\omega)$ is the leakage probability on consistent tuples and $0$ elsewhere (Eq. (4.6)). The **consistency projection** keeps the consistent entries and zeroes the others; the **sign table** is $J(\omega)=1/2$ if $\ell\cdot r=\ell'\cdot r'$ and $-1/2$ otherwise. For an orthonormal expansion of $\mathrm{prob}_z$ and a threshold $\beta$, the **residual** is
--   $$\Delta_z=\mathrm{prob}_z-2\cdot\mathrm{project}\big(\mathrm{prob}_z^{>\beta}\big).$$
--   For a matrix $M$, $F^M(\ell,r)=F((\ell,\ell M),(r,M^{-1}r))$. For labels $s,s'$, $\|F\|_{2,\mu_s\otimes\mu_{s'}}$ is the root-mean-square of $F(x,x')$ for independent $x\leftarrow\mu_s$, $x'\leftarrow\mu_{s'}$. With $q=2^n-1$, $\mathrm{disc}_n=3/\sqrt{q-1}$. Finally, a table $G$ is a **local approximation** of $\mathrm{prob}_z$ with parameters $(\beta,\varepsilon)$ if it has a product representation with energies $\Phi,\Psi$ such that
--   $\|G\|_*\le4$, $\Phi\le2/\beta$ and $\Psi\le2/\beta$ pointwise, $\mathbb E[\Phi]\le4$, $\mathbb E[\Psi]\le4$, $\|\mathrm{prob}_z-G\|_{2,\mu_s\otimes\mu_s}\le\varepsilon$ for both $s$, and $\|G\|_{2,\mu_s\otimes\mu_{s'}}\le6$ for all four label pairs (the conclusions (4.58)–(4.64) of Lemma 4.13).
--
--   **Formalization Note.** `ansProb lp z x x'` is the number of invertible $M$ with $(\ell M, M^{-1}r)=x'$ and answer $z$, divided by the number of invertible $M$ with $(\ell M,M^{-1}r)=x'$; when no matrix connects $x$ to $x'$ (an inconsistent pair) this is $0/0=0$ in Lean, which is the paper's extension by $0$. `probTable lp z ((ℓ,ℓ'),(r,r')) = ansProb lp z (ℓ,r) (ℓ',r')`. `consistent`, `project`, `signJ`, `residual E β`, `atMatrix F M`, `rmsMu n s s' F`, `disc n` and `IsLocalApprox lp z β ε G` are the objects above.
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), p. 28, Definition 4.2; pp. 29–30, Definitions 4.4, 4.5 and Eqs. (4.6)–(4.8); p. 32 (F^M); p. 35, Eq. (4.30); p. 40 (‖·‖_{2,ρ}); p. 41, Lemma 4.13 (4.58)–(4.64); p. 43 (disc_n)

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding
import Definitions.Def_LeakageRefresh_Continual_LeakageModel
import Definitions.Def_LeakageRefresh_Continual_Tables

/-!
# One refresh: leakage probability tables, consistency, the residual and local approximations

Dziembowski, Faust, *Leakage-Resilient Computation via Matrix Refreshing*, arXiv:2611.04876
(sha256 fdbb2454…), §4.2 Definition 4.2 (p. 28); §4.3: Definitions 4.4, 4.5, Eqs. (4.6)–(4.8)
(pp. 29–30), `F^M` (p. 32), Eq. (4.30) (p. 35); §4.3.4 `‖·‖_{2,ρ}` (p. 40); Lemma 4.13
(p. 41); §4.5 `disc_n` (p. 43).

* `Tuple4 n`, `Table4 n`: four-share tuples `ω = ((ℓ, ℓ′), (r, r′)) ∈ U_L² × U_R²` and real tables
  on them, rows `(ℓ, ℓ′) ∈ U_L²`, columns `(r, r′) ∈ U_R²`. A state pair `(x, x′)` with
  `x = (ℓ, r)`, `x′ = (ℓ′, r′)` is the tuple `((ℓ, ℓ′), (r, r′))`.
* `ansProb lp z x x′ = P_{M ←$ InvMatr}[Z = z | ℓ · M = ℓ′, M⁻¹ · r = r′]` (Definition 4.2,
  Eq. (4.3)): the number of matrices taking `x` to `x′` with answer `z`, divided by the number of
  matrices taking `x` to `x′`. When no matrix takes `x` to `x′` (an inconsistent tuple) the
  quotient is `0 / 0 = 0`, which is the paper's extension by `0` (Eq. (4.6)).
* `probTable lp z` is the table `prob_z` of Eq. (4.6); `consistent`, `project` are
  Definitions 4.4, 4.5; `signJ` is the table `J` of Eq. (4.30); `residual E β` is
  `∆_z = prob_z − 2 · project(prob_z^{>β})` (Eq. (4.8)) for an orthonormal expansion `E` of
  `prob_z`.
* `atMatrix F M (ℓ, r) = F((ℓ, ℓ · M), (r, M⁻¹ · r))` is `F^M` (p. 32).
* `rmsMu s s′ F = ‖F‖_{2, µₛ ⊗ µₛ′}`: the root-mean-square of `F(x, x′)` for independent
  `x ←$ µₛ`, `x′ ←$ µₛ′` (p. 40).
* `disc n = 3 / √(q − 1)` with `q = 2ⁿ − 1` (p. 43).
* `IsLocalApprox lp z β ε G`: the conclusions (4.58)–(4.64) of Lemma 4.13 for the table `G`
  and the leakage pair `lp`, answer `z`, with parameters `β`, `ε`.
-/

namespace LeakageRefresh.Continual

/-- Four-share tuples `((ℓ, ℓ′), (r, r′)) ∈ U_L² × U_R²` (Definition 4.4). -/
abbrev Tuple4 (n : ℕ) := (UL n × UL n) × (UR n × UR n)

/-- Real tables on `U_L² × U_R²`: rows `(ℓ, ℓ′)`, columns `(r, r′)`. -/
abbrev Table4 (n : ℕ) := Table (UL n × UL n) (UR n × UR n)

/-- The leakage probability function (Definition 4.2, Eq. (4.3)):
`P_{M ←$ InvMatr}[Z = z | ℓ · M = ℓ′, M⁻¹ · r = r′]` for the leakage pair `lp`, old state
`x = (ℓ, r)` and new state `x′ = (ℓ′, r′)`; `0` when no invertible matrix takes `x` to `x′`. -/
noncomputable def ansProb {n lam : ℕ} (lp : LeakPair n lam) (z : Answer lam)
    (x x' : State n) : ℝ :=
  ((Finset.univ.filter (fun M : InvMatr n => refreshState M x = x' ∧ answer lp x M = z)).card : ℝ) /
    ((Finset.univ.filter (fun M : InvMatr n => refreshState M x = x')).card : ℝ)

/-- The table `prob_z((ℓ, ℓ′), (r, r′))` of Eq. (4.6): the leakage probability of the answer `z`
on consistent tuples, `0` on inconsistent ones. -/
noncomputable def probTable {n lam : ℕ} (lp : LeakPair n lam) (z : Answer lam) : Table4 n :=
  fun p q => ansProb lp z (p.1, q.1) (p.2, q.2)

/-- A four-share tuple is consistent when `ℓ′ · r′ = ℓ · r` (Definition 4.4). -/
def consistent {n : ℕ} (ω : Tuple4 n) : Prop :=
  secret (ω.1.2, ω.2.2) = secret (ω.1.1, ω.2.1)

instance {n : ℕ} (ω : Tuple4 n) : Decidable (consistent ω) := by
  unfold consistent; infer_instance

/-- The consistency projection (Definition 4.5): keep the consistent entries, zero the rest. -/
noncomputable def project {n : ℕ} (F : Table4 n) : Table4 n :=
  fun p q => if consistent (p, q) then F p q else 0

/-- The consistency sign table `J` (Eq. (4.30)): `1/2` where `ℓ · r = ℓ′ · r′`, `−1/2`
elsewhere. -/
noncomputable def signJ (n : ℕ) : Table4 n :=
  fun p q => if consistent (p, q) then (1 / 2 : ℝ) else -(1 / 2 : ℝ)

/-- The residual `∆_z = prob_z − 2 · project(prob_z^{>β})` (Eq. (4.8)), for an orthonormal
expansion `E` of `prob_z` and the threshold `β`. -/
noncomputable def residual {n lam : ℕ} {lp : LeakPair n lam} {z : Answer lam}
    (E : OrthoExpansion (probTable lp z)) (β : ℝ) : Table4 n :=
  fun p q => probTable lp z p q - 2 * project (E.trunc β) p q

/-- `F^M(ℓ, r) = F((ℓ, ℓ · M), (r, M⁻¹ · r))`: a four-share table along the refresh by `M`
(p. 32). -/
def atMatrix {n : ℕ} (F : Table4 n) (M : InvMatr n) : Table (UL n) (UR n) :=
  fun ℓ r => F (ℓ, refreshL M ℓ) (r, refreshR M r)

/-- `‖F‖_{2, µₛ ⊗ µₛ′}` (p. 40): the root-mean-square of `F(x, x′) = F((ℓ, ℓ′), (r, r′))` for
independent `x = (ℓ, r) ←$ µₛ` and `x′ = (ℓ′, r′) ←$ µₛ′`. -/
noncomputable def rmsMu (n : ℕ) (s s' : ZMod 2) (F : Table4 n) : ℝ :=
  Real.sqrt (∑ x : State n, ∑ x' : State n,
    mu n s x * mu n s' x' * F (x.1, x'.1) (x.2, x'.2) ^ 2)

/-- The one-encoding discrepancy bound `disc_n = 3 / √(q − 1)`, `q = 2ⁿ − 1` (p. 43). -/
noncomputable def disc (n : ℕ) : ℝ :=
  3 / Real.sqrt (((2 : ℝ) ^ n - 1) - 1)

/-- The conclusions (4.58)–(4.64) of Lemma 4.13 for one round, with threshold `β` and error `ε`:
`G` has a product representation whose energies satisfy `‖G‖_* ≤ 4`, `Φ ≤ 2/β`, `Ψ ≤ 2/β`
pointwise, `E[Φ] ≤ 4`, `E[Ψ] ≤ 4`; `‖prob_z − G‖_{2, µₛ⊗µₛ} ≤ ε` for both `s`; and
`‖G‖_{2, µₛ⊗µₛ′} ≤ 6` for all four label pairs. -/
def IsLocalApprox {n lam : ℕ} (lp : LeakPair n lam) (z : Answer lam) (β ε : ℝ)
    (G : Table4 n) : Prop :=
  ∃ R : ProdRep G,
    nuclearNorm G ≤ 4 ∧
    (∀ x, R.Φ x ≤ 2 / β) ∧
    (∀ y, R.Ψ y ≤ 2 / β) ∧
    avg R.Φ ≤ 4 ∧
    avg R.Ψ ≤ 4 ∧
    (∀ s : ZMod 2, rmsMu n s s (fun p q => probTable lp z p q - G p q) ≤ ε) ∧
    (∀ s s' : ZMod 2, rmsMu n s s' G ≤ 6)

end LeakageRefresh.Continual


