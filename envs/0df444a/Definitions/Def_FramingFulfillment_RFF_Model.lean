-- Prove2me | Definitions.Def_FramingFulfillment_RFF_Model
-- name    : FramingFulfillment_RFF_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:00.213188+00:00
-- url     : https://prove2.me/theorems/bb803b2c-148b-4a75-ab7e-69ca2a38b910
-- title:
--   §3.1, §4, §5 — MNL framing with regions and FCs, DET' (10), OPT' value 𝒥*, framing matrices, ConstrDist and the RFF policy
-- statement:
--   This file sets up the joint framing and fulfillment (JFF) model of Lei, Jasin, Uichanco and Vakhutinsky and every object that their Theorem 2 mentions.
--
--   1. **Instance.** There are $I$ products, $J$ customer regions, $K$ fulfillment centers (FCs), $R$ framing groups and a horizon of $T$ periods. A customer from region $j$ arrives in a period with probability $\lambda_j$. Product $i$ shown to a region-$j$ customer in group $r$ has MNL attraction $v_{ijr}$ and price $p_{ir}$. Shipping product $i$ from FC $k$ to region $j$ costs $c_{ijk}$. Group $r$ holds at most $Q_r$ products, and FC $k$ starts with $C_{ik}$ units of product $i$. Group $R$ is the "no display" group.
--   2. **Standing assumptions.** $I,J,K\ge 1$ and $R\le I$. Each $\lambda_j\in[0,1]$ and $\sum_j\lambda_j\le 1$. $v_{ijr}>0$ for $r\ne R$ and $v_{ijR}=0$. Each $Q_r$ is a positive integer, and $Q_R\ge I$.
--   3. **Scaling.** For $\theta\in\mathbb N$, the scaled instance has horizon $T(\theta)=\theta T$ and inventories $C(\theta)=\theta C$. Everything else is unchanged.
--   4. **MNL quantities.** The no-purchase attraction is $v_{0j}=1$. For a fractional framing $x\in[0,1]^{I\times R}$ of region $j$,
--   $$\theta_{ij}(x)=\lambda_j\frac{\sum_r v_{ijr}x_{ir}}{1+\sum_{\ell,r}v_{\ell jr}x_{\ell r}},\qquad \mathcal R_{ij}(x)=\lambda_j\frac{\sum_r v_{ijr}x_{ir}p_{ir}}{1+\sum_{\ell,r}v_{\ell jr}x_{\ell r}}.$$
--      For an assignment $\phi:[I]\to[R]$, write $v_{ij}(\phi)=v_{ij\phi(i)}$. Then $\theta_{ij}(\phi)=\lambda_j v_{ij}(\phi)/(1+\sum_k v_{kj}(\phi))$ and $\mathcal R_{ij}(\phi)=\lambda_j v_{ij}(\phi)p_{i\phi(i)}/(1+\sum_k v_{kj}(\phi))$. The feasible assignments are $\Omega(Q)=\{\phi:\#\{i:\phi(i)=r\}\le Q_r\ \forall r\}$.
--   5. **DET' (10).** The variables are $x^t_j\in\mathbb R^{I\times R}$ and $y^t_j\in\mathbb R^{I\times K}$. The program maximizes $\sum_{t,i,j}\mathcal R_{ij}(x^t_j)-\sum_{t,j,i,k}c_{ijk}y^t_{ijk}$ subject to
--      - (10a) $\sum_i x^t_{ijr}\le Q_r$;
--      - (10b) $\sum_r x^t_{ijr}=1$;
--      - (10c) $\sum_k y^t_{ijk}=\theta_{ij}(x^t_j)$;
--      - (10d) $\sum_{t,j}y^t_{ijk}\le C_{ik}$;
--      - (10e) $x,y\in[0,1]$.
--
--      Its optimal value $\mathcal J^D$ is the supremum of the objective over the feasible set. A solution is *optimal* if it is feasible and attains that maximum.
--   6. **$\mathcal J^*$.** The optimal expected profit of OPT' (8) is defined by its dynamic program over (periods left, inventory vector). With probability $\lambda_j$ a region-$j$ customer arrives. The retailer chooses $\phi\in\Omega(Q)$ that puts every product out of stock in all FCs into group $R$. The customer buys $i$ with probability $v_{ij}(\phi)/(1+\sum_k v_{kj}(\phi))$ and pays $p_{i\phi(i)}$. The retailer then ships from an FC holding product $i$, pays $c_{ijk}$ and removes one unit. $\mathcal J^*$ is the value at the full horizon and the initial inventory.
--   7. **Framing matrices (Definition 1).** $B\in\mathbb R^{N\times R}$ is a framing matrix with respect to $\tilde Q\in\mathbb N^R$ if every row sums to $1$ and column $r$ sums to $\tilde Q_r$. It is integral if its entries are $0$ or $1$.
--   8. **ConstrDist.**
--      - **C1.** Let $q_r=\sum_i x_{ir}$, $\tilde Q_r=\lceil q_r\rceil$ and $\tilde I=\sum_r\lceil q_r\rceil-I$. Let $B$ be the $(I+\tilde I)\times R$ matrix with rows $x_{i\cdot}$ followed by $\tilde I$ fictitious rows $(\lceil q_r\rceil-q_r)/\tilde I$.
--      - **C1(iii).** A *framing decomposition* writes $B=\sum_\ell\alpha_\ell B^{(\ell)}$ with $\alpha_\ell\in(0,1]$, $\sum_\ell\alpha_\ell=1$ and each $B^{(\ell)}$ an integral framing matrix with respect to $\tilde Q$.
--      - **C2.** $\tilde\rho(\phi)=\sum_{\ell:\phi^{(\ell)}=\phi}\alpha_\ell$, where $\phi^{(\ell)}(i)=r$ iff $B^{(\ell)}_{ir}=1$.
--      - **C3.** For region $j$ and $\phi\in\Omega(Q)$,
--   $$\rho_j(\phi)=\tilde\rho(\phi)\,\frac{1+\sum_i v_{ij}(\phi)}{1+\sum_{\phi'\in\Omega(Q)}\tilde\rho(\phi')\sum_i v_{ij}(\phi')},$$
--        and $\rho_j(\phi)=0$ off $\Omega(Q)$.
--   9. **RFF and $\mathcal J^{RFF}$.** Fix a DET' solution $(x^{t,D},y^{t,D})$ and a framing decomposition of $B(x^{t,D}_j)$ for every $t$ and $j$; let $\rho^t_j$ be the resulting distributions. In period $t$:
--      - a region-$j$ customer arrives with probability $\lambda_j$;
--      - the retailer draws $\phi\sim\rho^t_j$ and shows $\tilde\phi$, which moves every product out of stock in all FCs into group $R$;
--      - the customer buys $i$ with probability $v_{ij}(\tilde\phi)/(1+\sum_k v_{kj}(\tilde\phi))$ at price $p_{i\tilde\phi(i)}$;
--      - an FC $k$ is drawn with probability $\tilde y_{ijk}=y^{t,D}_{ijk}/\sum_{k'}y^{t,D}_{ijk'}$;
--      - the order ships from $k$ if $k$ holds product $i$, and otherwise from the cheapest FC that does. The cost is paid and one unit is removed.
--
--      $\mathcal J^{RFF}$ is the exact expected total profit of this policy, computed by backward recursion over (period, inventory).
--
--   These are the objects of Theorem 2 and of the lemmas it uses: Lemma 2 and Lemma 3 are about ConstrDist, Lemma 5 compares $\mathcal J^*$ with $\mathcal J^D$, and Theorem 2 compares $\mathcal J^{RFF}$ with $\mathcal J^D$.
--
--   **Formalization Note**
--   - **Indexing.** Indices are `Fin` types, and the no-display group is the last index of `Fin R`. Inventories are vectors in $\mathbb N^{I\times K}$.
--   - **Expectations.** These are exact finite backward recursions; no measure theory is used.
--   - **Defaults never used under the standing assumptions.** A maximum over an empty finite set is $0$; it never occurs, because the all-no-display assignment is admissible and a displayed product is in stock somewhere. $\tilde y$ uses $0/0=0$; this is harmless because $\sum_{k'}y_{ijk'}=\theta_{ij}(x)=0$ with $\lambda_j>0$ forces every $\phi$ in the support of $\rho_j$ to hide product $i$.
--   - **Hypotheses added relative to the page.**
--     - $\sum_j\lambda_j\le 1$: the formal reading of "at most one customer arrives in each period".
--     - $v_{ijR}=0$ and $v_{ijr}>0$ otherwise: the page has $v=\exp(u)$ and says products in group $R$ have zero demand.
--     - $Q_R\ge I$: not on the page; without it RFF's step (iii) can be infeasible.
--     - $\theta\in\mathbb N$: $T(\theta)$ must be an integer.
--   - **Conventions.** The FC set in (8c) is $[K]$; the page's "FC 0" is never defined. Ties among cheapest FCs in RFF step (vii) are broken by least index. $\mathcal J^*$ is defined by the Bellman recursion of OPT', not by a maximum over measurable policies.
-- source:
--   Lei, Jasin, Uichanco & Vakhutinsky, Joint Product Framing and Order Fulfillment under the MNL Model, SSRN 3282019 (PDF sha256 7d6bd797…), pp. 7–9 (§3.1, (1)–(2)), 12 (Ω(Q), θ_i(φ), R_i(φ)), 14 (Definition 1), 15–16 (ConstrDist), 21–23 (§5: OPT' (8), DET' (10), RFF)

import Mathlib

namespace FramingFulfillment.RFF

open Finset

/-! # Joint framing and fulfillment under MNL (Lei–Jasin–Uichanco–Vakhutinsky)

Model of §3.1 and §5 (pp. 7–9, 21–23), the deterministic counterpart DET' (10), the
optimal value 𝒥* of OPT' (8) as its dynamic program, framing matrices (Definition 1, p. 14),
the distribution-construction procedure ConstrDist (pp. 15–16), and the expected profit of
the Randomized Framing and Fulfillment (RFF) policy (p. 23). -/

/-- A problem instance of the joint framing and fulfillment (JFF) problem (§3.1, §5):
`I` products, `J` regions, `K` fulfillment centers, `R` framing groups, horizon `T`;
arrival probabilities `lam j` (λ_j), MNL attractions `v i j r` (v_ijr), prices `p i r` (p_ir),
shipping costs `c i j k` (c_ijk), group cardinalities `Q r` (Q_r) and initial inventories
`C i k` (C_ik). The last group `⟨R - 1, _⟩` is the "no display" group `R` of p. 8. -/
structure Inst where
  I : ℕ
  J : ℕ
  K : ℕ
  R : ℕ
  T : ℕ
  hR : 0 < R
  lam : Fin J → ℝ
  v : Fin I → Fin J → Fin R → ℝ
  p : Fin I → Fin R → ℝ
  c : Fin I → Fin J → Fin K → ℝ
  Q : Fin R → ℕ
  C : Fin I → Fin K → ℕ

namespace Inst

variable (P : Inst)

/-- The "no display" group (group `R` of p. 8), the last index of `Fin R`. -/
def noDisp : Fin P.R := ⟨P.R - 1, by have := P.hR; omega⟩

/-- The standing assumptions of §3.1 and §5:
`I, J, K ≥ 1`; `R ≤ I` (p. 8, "a general model for any R ≤ I");
`λ_j ∈ [0,1]` and `∑_j λ_j ≤ 1` (at most one customer per period, p. 7);
`v_ijr > 0` for every displayed group and `v_ijR = 0` for the no-display group (pp. 8–9);
`Q_r ∈ ℕ₊` (p. 8); and `Q_R ≥ I` (not on the page: it lets every product be hidden). -/
def Standing : Prop :=
  0 < P.I ∧ 0 < P.J ∧ 0 < P.K ∧ P.R ≤ P.I ∧
  (∀ j, 0 ≤ P.lam j ∧ P.lam j ≤ 1) ∧ (∑ j, P.lam j) ≤ 1 ∧
  (∀ i j r, r ≠ P.noDisp → 0 < P.v i j r) ∧ (∀ i j, P.v i j P.noDisp = 0) ∧
  (∀ r, 0 < P.Q r) ∧ P.I ≤ P.Q P.noDisp

/-- The scaled instance of p. 13: `T(θ) = θ T`, `C(θ) = θ C`, all else unchanged. -/
def scale (θ : ℕ) : Inst :=
  { P with T := θ * P.T, C := fun i k => θ * P.C i k }

/-! ## MNL quantities (p. 12 and p. 21), with `v_0j = 1` -/

/-- `θ_ij(x) = λ_j ∑_r v_ijr x_ir / (1 + ∑_{ℓ,r} v_ℓjr x_ℓr)` for a fractional framing `x`
of region `j` (p. 21). -/
noncomputable def thetaX (j : Fin P.J) (x : Fin P.I → Fin P.R → ℝ) (i : Fin P.I) : ℝ :=
  P.lam j * (∑ r, P.v i j r * x i r) / (1 + ∑ l, ∑ r, P.v l j r * x l r)

/-- `R_ij(x) = λ_j ∑_r v_ijr x_ir p_ir / (1 + ∑_{ℓ,r} v_ℓjr x_ℓr)` (p. 21). -/
noncomputable def revX (j : Fin P.J) (x : Fin P.I → Fin P.R → ℝ) (i : Fin P.I) : ℝ :=
  P.lam j * (∑ r, P.v i j r * x i r * P.p i r) / (1 + ∑ l, ∑ r, P.v l j r * x l r)

/-- `v_ij(φ) = v_{ij φ(i)}` for a framing assignment `φ : [I] → [R]` (p. 12). -/
def vPhi (j : Fin P.J) (φ : Fin P.I → Fin P.R) (i : Fin P.I) : ℝ := P.v i j (φ i)

/-- `θ_ij(φ) = λ_j v_ij(φ) / (1 + ∑_k v_kj(φ))` (p. 12, region `j` added as in §5). -/
noncomputable def thetaPhi (j : Fin P.J) (φ : Fin P.I → Fin P.R) (i : Fin P.I) : ℝ :=
  P.lam j * P.vPhi j φ i / (1 + ∑ k, P.vPhi j φ k)

/-- `R_ij(φ) = λ_j v_ij(φ) p_{iφ(i)} / (1 + ∑_k v_kj(φ))` (p. 12, region `j` added). -/
noncomputable def revPhi (j : Fin P.J) (φ : Fin P.I → Fin P.R) (i : Fin P.I) : ℝ :=
  P.lam j * P.vPhi j φ i * P.p i (φ i) / (1 + ∑ k, P.vPhi j φ k)

/-- Purchase probability of product `i` by a customer from region `j` who has arrived and sees
assignment `φ`: `v_ij(φ) / (1 + ∑_k v_kj(φ))`. -/
noncomputable def buyProb (j : Fin P.J) (φ : Fin P.I → Fin P.R) (i : Fin P.I) : ℝ :=
  P.vPhi j φ i / (1 + ∑ k, P.vPhi j φ k)

/-- `Ω(Q) = {φ ∈ [R]^I : ∑_i 1{φ(i) = r} ≤ Q_r ∀ r}` (p. 12). -/
def Omega : Finset (Fin P.I → Fin P.R) :=
  univ.filter (fun φ => ∀ r, (univ.filter (fun i => φ i = r)).card ≤ P.Q r)

end Inst

/-! ## DET' (10), p. 22 -/

/-- Decision variables of DET': `x t j i r` (x^t_ijr) and `y t j i k` (y^t_ijk). -/
structure DETSol (P : Inst) where
  x : Fin P.T → Fin P.J → Fin P.I → Fin P.R → ℝ
  y : Fin P.T → Fin P.J → Fin P.I → Fin P.K → ℝ

namespace Inst

variable (P : Inst)

/-- Feasible set of DET' (10a)–(10e). -/
def DETFeasible : Set (DETSol P) :=
  {s | (∀ t j r, ∑ i, s.x t j i r ≤ (P.Q r : ℝ)) ∧
       (∀ t j i, ∑ r, s.x t j i r = 1) ∧
       (∀ t j i, ∑ k, s.y t j i k = P.thetaX j (s.x t j) i) ∧
       (∀ i k, ∑ t, ∑ j, s.y t j i k ≤ (P.C i k : ℝ)) ∧
       (∀ t j i r, 0 ≤ s.x t j i r ∧ s.x t j i r ≤ 1) ∧
       (∀ t j i k, 0 ≤ s.y t j i k ∧ s.y t j i k ≤ 1)}

/-- Objective of DET': `∑_{t,i,j} R_ij(x^t_j) − ∑_{t,j} c_j · y^t_j`. -/
noncomputable def detObj (s : DETSol P) : ℝ :=
  (∑ t, ∑ i, ∑ j, P.revX j (s.x t j) i) - ∑ t, ∑ j, ∑ i, ∑ k, P.c i j k * s.y t j i k

/-- `𝒥^D`, the optimal value of DET'. -/
noncomputable def JD : ℝ := sSup (P.detObj '' P.DETFeasible)

/-- `s` is an optimal solution of DET'. -/
def IsDETOpt (s : DETSol P) : Prop :=
  s ∈ P.DETFeasible ∧ ∀ s' ∈ P.DETFeasible, P.detObj s' ≤ P.detObj s

/-! ## Inventory states and the optimal value 𝒥* of OPT' (8) -/

/-- Inventory vectors `C ∈ ℕ^{I × K}`. -/
abbrev Inv := Fin P.I → Fin P.K → ℕ

/-- Maximum of `f` over a finite set, `0` on the empty set (never used under `Standing`). -/
noncomputable def finMax {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  if h : s.Nonempty then s.sup' h f else 0

/-- Remove one unit of product `i` from FC `k`. -/
def take (C : P.Inv) (i : Fin P.I) (k : Fin P.K) : P.Inv :=
  fun i' k' => if i' = i ∧ k' = k then C i k - 1 else C i' k'

/-- Assignments allowed at inventory `C`: feasible (`Ω(Q)`) and showing no product that is out
of stock in every FC (constraints (8c)–(8d) holding almost surely). -/
def admissible (C : P.Inv) : Finset (Fin P.I → Fin P.R) :=
  P.Omega.filter (fun φ => ∀ i, ∑ k, C i k = 0 → φ i = P.noDisp)

/-- The dynamic program of OPT' (p. 21; p. 10: π* "can be computed exactly by solving a Dynamic
Programming"): `optValue n C` is the optimal expected profit with `n` periods left and
inventory `C`. In each period a customer arrives from region `j` with probability `λ_j`; the
retailer picks an admissible assignment `φ`; the customer buys `i` with probability
`v_ij(φ)/(1 + ∑_k v_kj(φ))` and pays `p_{iφ(i)}`; the retailer then ships from an FC `k` with
`C_ik > 0`, paying `c_ijk`. -/
noncomputable def optValue : ℕ → P.Inv → ℝ
  | 0, _ => 0
  | n + 1, C =>
      (1 - ∑ j, P.lam j) * optValue n C +
      ∑ j, P.lam j * finMax (P.admissible C) (fun φ =>
        (∑ i, P.buyProb j φ i *
            (P.p i (φ i) + finMax (univ.filter (fun k => 0 < C i k))
              (fun k => optValue n (P.take C i k) - P.c i j k))) +
        (1 - ∑ i, P.buyProb j φ i) * optValue n C)

/-- `𝒥*`, the optimal expected profit of OPT' (8). -/
noncomputable def Jstar : ℝ := P.optValue P.T P.C

end Inst

/-! ## Framing matrices (Definition 1, p. 14) and ConstrDist (pp. 15–16) -/

/-- Definition 1: `B ∈ ℝ^{N×R}` is a framing matrix w.r.t. `Q̃ ∈ ℕ^R` if every row sums to 1
and column `r` sums to `Q̃_r`. -/
def IsFramingMatrix {N R : ℕ} (B : Fin N → Fin R → ℝ) (Qt : Fin R → ℕ) : Prop :=
  (∀ n, ∑ r, B n r = 1) ∧ (∀ r, ∑ n, B n r = (Qt r : ℝ))

/-- A matrix is integral if its entries are 0 or 1 (p. 14). -/
def IsIntegralMatrix {N R : ℕ} (B : Fin N → Fin R → ℝ) : Prop :=
  ∀ n r, B n r = 0 ∨ B n r = 1

/-- `B = ∑_ℓ α_ℓ B^(ℓ)` with `α_ℓ ∈ (0,1]`, `∑ α_ℓ = 1`, and each `B^(ℓ)` an integral framing
matrix w.r.t. `Q̃` (ConstrDist C1(iii), p. 15). -/
def IsFramingDecomposition {N R L : ℕ} (B : Fin N → Fin R → ℝ) (Qt : Fin R → ℕ)
    (α : Fin L → ℝ) (Bs : Fin L → Fin N → Fin R → ℝ) : Prop :=
  (∀ l, 0 < α l ∧ α l ≤ 1) ∧ (∑ l, α l = 1) ∧
  (∀ l, IsIntegralMatrix (Bs l) ∧ IsFramingMatrix (Bs l) Qt) ∧
  (∀ n r, B n r = ∑ l, α l * Bs l n r)

/-- C1(i): `q_r = ∑_i x_ir`. -/
def qSum {I R : ℕ} (x : Fin I → Fin R → ℝ) (r : Fin R) : ℝ := ∑ i, x i r

/-- C1(i): `Q̃_r = ⌈q_r⌉`. -/
noncomputable def Qtil {I R : ℕ} (x : Fin I → Fin R → ℝ) (r : Fin R) : ℕ := ⌈qSum x r⌉₊

/-- C1(i): `Ĩ = ∑_r ⌈q_r⌉ − I`. -/
noncomputable def Itil {I R : ℕ} (x : Fin I → Fin R → ℝ) : ℕ := (∑ r, Qtil x r) - I

/-- C1(ii): the `(I + Ĩ) × R` matrix with `B_ir = x_ir` for the `I` real products and
`B_ir = (⌈q_r⌉ − q_r)/Ĩ` for the `Ĩ` fictitious products. -/
noncomputable def Bmat {I R : ℕ} (x : Fin I → Fin R → ℝ) : Fin (I + Itil x) → Fin R → ℝ :=
  Fin.addCases (motive := fun _ => Fin R → ℝ) (fun i r => x i r)
    (fun _ r => ((Qtil x r : ℝ) - qSum x r) / (Itil x : ℝ))

/-- A framing decomposition of `B(x)` (ConstrDist C1(iii)): any weights and integral framing
matrices with `B(x) = ∑_ℓ α_ℓ B^(ℓ)`. Not unique. -/
structure FramingDecomp {I R : ℕ} (x : Fin I → Fin R → ℝ) where
  L : ℕ
  α : Fin L → ℝ
  B : Fin L → Fin (I + Itil x) → Fin R → ℝ
  isDecomp : IsFramingDecomposition (Bmat x) (Qtil x) α B

open scoped Classical in
/-- C1(iv)–C2: `ρ̃(φ) = ∑_{ℓ : φ^(ℓ) = φ} α_ℓ`, where `φ^(ℓ)(i) = r` iff `B^(ℓ)_ir = 1`
(`i ≤ I`). Duplicate `φ^(ℓ)` are summed. -/
noncomputable def rhoTil {I R : ℕ} {x : Fin I → Fin R → ℝ} (d : FramingDecomp x)
    (φ : Fin I → Fin R) : ℝ :=
  ∑ l, if (∀ i r, φ i = r ↔ d.B l (Fin.castAdd (Itil x) i) r = 1) then d.α l else 0

namespace Inst

variable (P : Inst)

/-- C3 (re-scaling), for region `j`:
`ρ(φ) = ρ̃(φ)(1 + ∑_i v_ij(φ)) / (1 + ∑_{φ'∈Ω(Q)} ρ̃(φ') ∑_i v_ij(φ'))` on `Ω(Q)`, and 0
elsewhere. -/
noncomputable def rho (j : Fin P.J) {x : Fin P.I → Fin P.R → ℝ} (d : FramingDecomp x)
    (φ : Fin P.I → Fin P.R) : ℝ :=
  if φ ∈ P.Omega then
    rhoTil d φ * (1 + ∑ i, P.vPhi j φ i) /
      (1 + ∑ φ' ∈ P.Omega, rhoTil d φ' * ∑ i, P.vPhi j φ' i)
  else 0

/-! ## The RFF policy (p. 23) -/

/-- RFF step 2(iii): `φ̃(i) = R` if product `i` is out of stock in every FC, else `φ(i)`. -/
def hideOut (C : P.Inv) (φ : Fin P.I → Fin P.R) : Fin P.I → Fin P.R :=
  fun i => if ∑ k, C i k = 0 then P.noDisp else φ i

/-- RFF step 2(vi): `ỹ_ijk = y_ijk / ∑_{k'} y_ijk'` (with `0/0 = 0`). -/
noncomputable def ytil (y : Fin P.I → Fin P.K → ℝ) (i : Fin P.I) (k : Fin P.K) : ℝ :=
  y i k / ∑ k', y i k'

/-- RFF step 2(vii): ship from the sampled FC `k` if it holds product `i`; otherwise from the
cheapest FC (for region `j`) that holds it, ties broken by least index. -/
noncomputable def fcChoice (C : P.Inv) (j : Fin P.J) (i : Fin P.I) (k : Fin P.K) : Fin P.K :=
  if 0 < C i k then k else
    if h : (univ.filter (fun k' => 0 < C i k')).Nonempty then
      ((univ.filter (fun k' => 0 < C i k')).filter
          (fun k' => P.c i j k' = (univ.filter (fun k' => 0 < C i k')).inf' h (P.c i j))).min'
        (by
          obtain ⟨k', hk', he⟩ :=
            (univ.filter (fun k' => 0 < C i k')).exists_mem_eq_inf' h (P.c i j)
          exact ⟨k', Finset.mem_filter.mpr ⟨hk', he.symm⟩⟩)
    else k

/-- Expected remaining profit of RFF built from the DET' solution `s` and the framing
decompositions `dec t j` of `B(x^t_j)`: `rffValue s dec n C` is the expected profit of
periods `T − n, …, T − 1` (0-based) from inventory `C`. In period `t`: a customer arrives from
region `j` with probability `λ_j` (none with probability `1 − ∑_j λ_j`); `φ ∼ ρ^t_j`; the
customer sees `φ̃ = hideOut C φ` and buys `i` with probability `v_ij(φ̃)/(1 + ∑_k v_kj(φ̃))`,
paying `p_{iφ̃(i)}`; an FC `k ∼ ỹ^t_{ij·}` is sampled and the order is shipped from
`fcChoice C j i k`, paying its cost and removing one unit. -/
noncomputable def rffValue (s : DETSol P) (dec : ∀ (t : Fin P.T) (j : Fin P.J),
    FramingDecomp (s.x t j)) : ℕ → P.Inv → ℝ
  | 0, _ => 0
  | n + 1, C =>
      if h : n + 1 ≤ P.T then
        (1 - ∑ j, P.lam j) * rffValue s dec n C +
        ∑ j, P.lam j * ∑ φ ∈ P.Omega,
          P.rho j (dec ⟨P.T - (n + 1), by omega⟩ j) φ *
            ((∑ i, P.buyProb j (P.hideOut C φ) i *
                (P.p i (P.hideOut C φ i) +
                  ∑ k, P.ytil (s.y ⟨P.T - (n + 1), by omega⟩ j) i k *
                    (rffValue s dec n (P.take C i (P.fcChoice C j i k)) -
                      P.c i j (P.fcChoice C j i k)))) +
             (1 - ∑ i, P.buyProb j (P.hideOut C φ) i) * rffValue s dec n C)
      else 0

/-- `𝒥^RFF`: the expected total profit of RFF over the horizon from the initial inventory. -/
noncomputable def JRFF (s : DETSol P) (dec : ∀ (t : Fin P.T) (j : Fin P.J),
    FramingDecomp (s.x t j)) : ℝ :=
  P.rffValue s dec P.T P.C

end Inst

end FramingFulfillment.RFF


