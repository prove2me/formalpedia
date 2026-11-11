-- Prove2me | Definitions.Def_SwapDisk_Main_Sharp
-- name    : SwapDisk_Main_Sharp
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:17:31.801554+00:00
-- url     : https://prove2.me/theorems/871b1016-5871-473b-a082-a911ea7beb8d
-- title:
--   SHARP's multiscale tagged dictionary: scales, nets, constraints $h_c$, $L_\kappa$, $F_\kappa$, rate grids, priors, product weights, $\Psi_t$, $\kappa_t$, budgets and response selectors
-- statement:
--   Fix $\gamma=2^{-\ell}$ ($\ell\in\mathbb N$; $\gamma\in\Gamma_T$ means $\ell\le\lfloor\log_2T\rfloor$). For $k=0,\dots,\ell$ put $s_k=2^k\gamma$, $r_k=2^{-3-\lceil k/2\rceil}$ and choose finite **angular $r_k$-nets** $X_k\subseteq S^1$ (every point of $S^1$ within arc distance $r_k$ of $X_k$) with $|X_k|\le16/r_k$; $n_k=|X_k|$. The tagged dictionary is $J=\{0\}\cup\{(k,x):x\in X_k\}$ with $x_0=0$, $x_{(k,x)}=x$, and $M=|J|$.
--
--   **Constraints.** A boundary tag $j=(k,x)$, $s=s_k$, carries $h_{j,\mathrm{rad}}(g)=s/2+\langle g,x\rangle$ and $h_{j,\pm}(g)=\pm\langle g,\tau_x\rangle-2sr_k$; the centre carries $h_{0,i,\sigma}(g)=\sigma g_i-\gamma$ ($i\in\{1,2\}$, $\sigma=\pm1$). With $j(c)$ the tag of $c$ and $\kappa\in\Delta(C)$, $c_j(\kappa)+\langle v_j(\kappa),g\rangle=\sum_{c:j(c)=j}\kappa_ch_c(g)$,
--   $$L_\kappa(q,g)=\sum_c\kappa_cq(j(c))h_c(g),\qquad F_\kappa(q)=\sum_jq(j)c_j(\kappa)+\Big\|\sum_jq(j)v_j(\kappa)\Big\|_2 .$$
--
--   **Rates, priors, weights.** A boundary constraint at level $k$ has rates $H_k=\{s_k2^{-\ell'}/16:0\le\ell'\le k\}$ and prior $\pi_{c,\eta}=2^{-k-2}/(3n_k(k+1))$; a centre constraint has the single rate $\gamma/16$ and prior $(2+\gamma)/16$. On a tag–loss history $(J_u,g_u)_{u<t}$, $f_{c,u}=1\{J_u=j(c)\}h_c(g_u)$, $S_c=\sum_uf_{c,u}$,
--   $$W_{c,\eta,t}=\pi_{c,\eta}\prod_{u<t}(1+\eta f_{c,u}),\quad\Psi_t=\sum_{c,\eta}W_{c,\eta,t},\quad Z_t=\sum_{c,\eta}\eta W_{c,\eta,t},\quad\kappa_c=\frac{\sum_\eta\eta W_{c,\eta,t}}{Z_t},$$
--   $U=\log(1+\Psi)$, $\lambda_k=\log(3n_k(k+1)2^{k+2})+U$, $\lambda^{\mathrm{ctr}}_0=\log8+U$. A **response selector with error $\epsilon$** is a Borel map $q$ with $q(\kappa)\in\Delta(J)$ and $L_\kappa(q(\kappa),g)\le\epsilon$ for all $\kappa\in\Delta(C)$, $g\in B^2_2$; SHARP's response after a history is $q_{1/T}(\kappa)$.
--
--   These objects define the algorithm whose master bound (Theorem 4.1) gives every upper bound of the mission.
--
--   **Formalization Note.** Levels are `Fin (ℓ + 1)`; tags are `Option (Σ k, X k)` (`none` is the centre); constraint kinds `rad`, `plus`, `minus`; centre constraints `(i, σ) : Fin 2 × Bool` (coordinate 0-based, `true` = $+1$). Each $h_c$ is written as `hconst c + ⟨hvec c, g⟩`. A pair at level $k$ is indexed by $\ell'\in$ `Fin (k + 1)`. Weights are the closed-form products of the recursion $W_{t}=W_{t-1}(1+\eta f_t)$. The simplex is $\{q\ge0,\sum q=1\}$; a selector is a Borel map `(C → ℝ) → (J → ℝ)` whose values off $\Delta(C)$ do not matter. `tagPt` sends a net point to itself through `toDisk` (net points have norm one).
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 21 (§B.1.1, Eqs. (B.1)–(B.4)), p. 22 (Eqs. (B.6)–(B.10)), p. 23 (Eq. (B.13)), p. 25 (Eqs. (B.18)–(B.22)), p. 26 (Eq. (B.26)), pp. 8–9 (Eqs. (4.1)–(4.3), Algorithm 4.1)

import Mathlib
import Definitions.Def_SwapDisk_Main_Regret

/-!
# SHARP: the multiscale tagged dictionary, its constraints, rates, priors and product weights

Saravanan, *Minimax Realized Full Swap Regret on the Euclidean Disk*, STOC 2027 submission
(manuscript sha256 e7138cc2…): p. 21 (§B.1.1, Eqs. (B.1)–(B.4)), p. 22 (Eqs. (B.6)–(B.10)),
p. 23 (Eq. (B.13)), p. 25 (Eqs. (B.18)–(B.22)), p. 26 (Eq. (B.26)); p. 8 (Eqs. (4.1)–(4.3)) and
p. 9 (Algorithm 4.1).

Conventions.
* The resolution `γ ∈ Γ_T = {2^{−k} : 0 ≤ k ≤ ⌊log₂ T⌋}` is encoded by its exponent
  `ℓ = ℓ_γ = log₂(1/γ)`, `γ = 2^{−ℓ}`; `γ ∈ Γ_T` is `ℓ ≤ Nat.log 2 T`.
* Levels `k = 0, …, ℓ` are `Fin (ℓ + 1)`; `s_k = 2^k γ`, `r_k = 2^{−3−⌈k/2⌉}`.
* The nets `X_k ⊆ S¹` are arbitrary finite sets (`Finset`), assumed in the theorems to be angular
  `r_k`-nets with `|X_k| ≤ 16/r_k` (Eq. (B.3)); angular distance of unit vectors is
  `arccos ⟨u, v⟩`, the length of the shorter arc.
* Tags: `J = {0} ∪ {(k, x) : x ∈ X_k}` is `Option (Σ k, X k)` (`none` is the centre tag);
  a point at several scales gives distinct tags. Attached points: `x_0 = 0`, `x_(k,x) = x`.
* Constraints: the four centre constraints `(i, σ)` (`i ∈ {0, 1}` for the paper's `k ∈ {1, 2}`,
  `σ ∈ {+1, −1}` as `Bool`) and three per boundary tag (radial, `+`, `−`). Each `h_c` is the affine
  map `g ↦ hconst c + ⟨hvec c, g⟩` with exactly the coefficients of Eqs. (B.6)–(B.7).
* Constraint–rate pairs: one per centre constraint (rate `γ/16`) and one per boundary constraint
  at level `k` and `ℓ' ∈ {0, …, k}` (rate `s_k 2^{−ℓ'}/16`).
* A tag–loss history of length `t` is `h : Fin t → J × Disk` (`(J_u, g_u)`); weights are the
  closed forms `W_{c,η,t} = π_{c,η} ∏_{u<t} (1 + η f_{c,u})` of the recursion (B.21).
* The simplex `Δ(I)` is `{q : I → ℝ | q ≥ 0, ∑ q = 1}`; a response selector is a Borel map
  `ℝ^C → ℝ^J` (its values off `Δ(C)` are irrelevant).
-/

open MeasureTheory

namespace SwapDisk.Main

/-- The probability simplex `Δ(ι)` over a finite type. -/
def simplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {q | (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1}

/-- The resolution `γ = 2^{−ℓ}`. -/
noncomputable def gam (ell : ℕ) : ℝ := (2 : ℝ) ^ (-(ell : ℤ))

/-- The scale `s_k = 2^k γ` (Eq. (B.1)). -/
noncomputable def scale (ell k : ℕ) : ℝ := (2 : ℝ) ^ k * gam ell

/-- The net radius `r_k = 2^{−3−⌈k/2⌉}` (Eq. (B.1)). -/
noncomputable def radius (k : ℕ) : ℝ := (2 : ℝ) ^ (-3 - ⌈(k : ℝ) / 2⌉)

/-- Angular distance on `S¹`: the length `arccos ⟨u, v⟩` of the shorter arc. -/
noncomputable def angDist (u v : E2) : ℝ := Real.arccos (ip u v)

/-- `X` is an angular `r`-net of `S¹`: `X ⊆ S¹` and every point of `S¹` is within angular
distance `r` of some point of `X`. -/
def IsAngularNet (r : ℝ) (X : Finset E2) : Prop :=
  (∀ x ∈ X, x ∈ unitCircle) ∧ ∀ u ∈ unitCircle, ∃ x ∈ X, angDist u x ≤ r

/-- Eq. (B.3) for every level: `X_k` is an angular `r_k`-net with `|X_k| ≤ 16/r_k`. -/
def NetsOK (ell : ℕ) (X : Fin (ell + 1) → Finset E2) : Prop :=
  ∀ k : Fin (ell + 1), IsAngularNet (radius k) (X k) ∧ ((X k).card : ℝ) ≤ 16 / radius k

/-- Boundary tags `(k, x)`, `x ∈ X_k`. -/
abbrev BTag (ell : ℕ) (X : Fin (ell + 1) → Finset E2) : Type := Σ k : Fin (ell + 1), ↥(X k)

/-- The tagged dictionary `J = {0} ∪ {(s, x) : s ∈ S_γ, x ∈ X_s}` (Eq. (B.4)); `none` is `0`. -/
abbrev Tag (ell : ℕ) (X : Fin (ell + 1) → Finset E2) : Type := Option (BTag ell X)

noncomputable instance (ell : ℕ) (X : Fin (ell + 1) → Finset E2) : DecidableEq (Tag ell X) :=
  Classical.decEq _

/-- Tags carry the discrete σ-field. -/
instance (ell : ℕ) (X : Fin (ell + 1) → Finset E2) : MeasurableSpace (Tag ell X) := ⊤

/-- The attached point `x_j`: `x_0 = 0`, `x_(s,x) = x`. -/
noncomputable def tagPt {ell : ℕ} {X : Fin (ell + 1) → Finset E2} : Tag ell X → Disk
  | none => ⟨0, by simp [disk]⟩
  | some b => toDisk (b.2 : E2)

/-- The three constraints of a boundary tag (Eq. (B.6)). -/
inductive BKind
  | rad
  | plus
  | minus
  deriving DecidableEq

instance : Fintype BKind :=
  ⟨{BKind.rad, BKind.plus, BKind.minus}, fun x => by cases x <;> simp⟩

/-- Constraint labels `C`: four centre constraints `(i, σ)` and three per boundary tag. -/
abbrev Con (ell : ℕ) (X : Fin (ell + 1) → Finset E2) : Type :=
  (Fin 2 × Bool) ⊕ (BTag ell X × BKind)

noncomputable instance (ell : ℕ) (X : Fin (ell + 1) → Finset E2) : DecidableEq (Con ell X) :=
  Classical.decEq _

/-- The tag `j(c)` carrying a constraint. -/
def conTag {ell : ℕ} {X : Fin (ell + 1) → Finset E2} : Con ell X → Tag ell X
  | .inl _ => none
  | .inr c => some c.1

/-- `σ ∈ {+1, −1}` from a Boolean. -/
def sgn (σ : Bool) : ℝ := if σ then 1 else -1

/-- Constant term of `h_c`: `−γ` (centre), `s/2` (radial), `−2 s r_s` (tangential). -/
noncomputable def hconst {ell : ℕ} {X : Fin (ell + 1) → Finset E2} : Con ell X → ℝ
  | .inl _ => -gam ell
  | .inr (b, .rad) => scale ell b.1 / 2
  | .inr (b, .plus) => -2 * scale ell b.1 * radius b.1
  | .inr (b, .minus) => -2 * scale ell b.1 * radius b.1

/-- Linear part of `h_c`: `σ e_i` (centre), `x` (radial), `τ_x` and `−τ_x` (tangential). -/
noncomputable def hvec {ell : ℕ} {X : Fin (ell + 1) → Finset E2} : Con ell X → E2
  | .inl (i, σ) => sgn σ • EuclideanSpace.single i 1
  | .inr (b, .rad) => (b.2 : E2)
  | .inr (b, .plus) => tau (b.2 : E2)
  | .inr (b, .minus) => -tau (b.2 : E2)

/-- The affine constraint `h_c(g) = hconst c + ⟨hvec c, g⟩` (Eqs. (B.6), (B.7)):
`h_rad(g) = s/2 + ⟨g, x⟩`, `h_±(g) = ±⟨g, τ_x⟩ − 2 s r_s`, `h_{0,i,σ}(g) = σ g_i − γ`. -/
noncomputable def hval {ell : ℕ} {X : Fin (ell + 1) → Finset E2} (c : Con ell X) (g : E2) : ℝ :=
  hconst c + ip (hvec c) g

/-- `c_j(κ) = ∑_{c : j(c) = j} κ_c hconst c` (Eq. (B.9)). -/
noncomputable def coefC {ell : ℕ} {X : Fin (ell + 1) → Finset E2} (κ : Con ell X → ℝ)
    (j : Tag ell X) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c => conTag c = j), κ c * hconst c

/-- `v_j(κ) = ∑_{c : j(c) = j} κ_c hvec c` (Eq. (B.9)). -/
noncomputable def coefV {ell : ℕ} {X : Fin (ell + 1) → Finset E2} (κ : Con ell X → ℝ)
    (j : Tag ell X) : E2 :=
  ∑ c ∈ Finset.univ.filter (fun c => conTag c = j), κ c • hvec c

/-- `L_κ(q, g) = ∑_c κ_c q(j(c)) h_c(g)` (Eq. (B.10)). -/
noncomputable def Lkappa {ell : ℕ} {X : Fin (ell + 1) → Finset E2} (κ : Con ell X → ℝ)
    (q : Tag ell X → ℝ) (g : E2) : ℝ :=
  ∑ c, κ c * q (conTag c) * hval c g

/-- `F_κ(q) = ∑_j q(j) c_j(κ) + ‖∑_j q(j) v_j(κ)‖₂` (Eq. (B.10)). -/
noncomputable def Fkappa {ell : ℕ} {X : Fin (ell + 1) → Finset E2} (κ : Con ell X → ℝ)
    (q : Tag ell X → ℝ) : ℝ :=
  ∑ j, q j * coefC κ j + ‖∑ j, q j • coefV κ j‖

/-- Constraint–rate pairs: one per centre constraint (rate `γ/16`), and for a boundary
constraint at level `k` one per `ℓ' ∈ {0, …, k}` (rate `s_k 2^{−ℓ'}/16`) (Eq. (B.18)). -/
abbrev Pair (ell : ℕ) (X : Fin (ell + 1) → Finset E2) : Type :=
  (Fin 2 × Bool) ⊕ (Σ c : BTag ell X × BKind, Fin (c.1.1.val + 1))

noncomputable instance (ell : ℕ) (X : Fin (ell + 1) → Finset E2) : DecidableEq (Pair ell X) :=
  Classical.decEq _

/-- The constraint of a pair. -/
def pairCon {ell : ℕ} {X : Fin (ell + 1) → Finset E2} : Pair ell X → Con ell X
  | .inl a => .inl a
  | .inr p => .inr p.1

/-- The rate `η` of a pair: `γ/16` (centre), `s_k 2^{−ℓ'}/16` (boundary, level `k`). -/
noncomputable def rate {ell : ℕ} {X : Fin (ell + 1) → Finset E2} : Pair ell X → ℝ
  | .inl _ => gam ell / 16
  | .inr p => scale ell p.1.1.1 * (2 : ℝ) ^ (-(p.2.val : ℤ)) / 16

/-- The prior `π_{c,η}`: `(2 + γ)/16` (centre), `2^{−k−2}/(3 n_k (k+1))` (boundary, level `k`,
`n_k = |X_k|`) (Eq. (B.19)). -/
noncomputable def prior {ell : ℕ} {X : Fin (ell + 1) → Finset E2} : Pair ell X → ℝ
  | .inl _ => (2 + gam ell) / 16
  | .inr p => (2 : ℝ) ^ (-(p.1.1.1.val : ℤ) - 2) /
      (3 * ((X p.1.1.1).card : ℝ) * ((p.1.1.1.val : ℝ) + 1))

/-- The scalar update `f_{c,u} = 1{J_u = j(c)} h_c(g_u)` (Eq. (B.13)). -/
noncomputable def fupd {ell : ℕ} {X : Fin (ell + 1) → Finset E2} (c : Con ell X)
    (jg : Tag ell X × Disk) : ℝ :=
  if jg.1 = conTag c then hval c (jg.2 : E2) else 0

/-- The certificate sum `S_c = ∑_t f_{c,t}` (Eq. (B.13)). -/
noncomputable def certSum {ell : ℕ} {X : Fin (ell + 1) → Finset E2} {t : ℕ}
    (h : Fin t → Tag ell X × Disk) (c : Con ell X) : ℝ :=
  ∑ u, fupd c (h u)

/-- The product weight `W_{c,η,t} = π_{c,η} ∏_{u<t} (1 + η f_{c,u})` (Eq. (B.21)). -/
noncomputable def weight {ell : ℕ} {X : Fin (ell + 1) → Finset E2} {t : ℕ}
    (h : Fin t → Tag ell X × Disk) (p : Pair ell X) : ℝ :=
  prior p * ∏ u, (1 + rate p * fupd (pairCon p) (h u))

/-- The potential `Ψ_t = ∑_{c,η} W_{c,η,t}` (Eq. (B.20)). -/
noncomputable def Psi {ell : ℕ} {X : Fin (ell + 1) → Finset E2} {t : ℕ}
    (h : Fin t → Tag ell X × Disk) : ℝ :=
  ∑ p, weight h p

/-- `Z_t = ∑_{c,η} η W_{c,η,t}` (Eq. (B.20)). -/
noncomputable def Zsum {ell : ℕ} {X : Fin (ell + 1) → Finset E2} {t : ℕ}
    (h : Fin t → Tag ell X × Disk) : ℝ :=
  ∑ p, rate p * weight h p

/-- The constraint weights `κ_c = ∑_η η W_{c,η} / Z` used in the next round (Eq. (B.20)). -/
noncomputable def kappa {ell : ℕ} {X : Fin (ell + 1) → Finset E2} {t : ℕ}
    (h : Fin t → Tag ell X × Disk) (c : Con ell X) : ℝ :=
  (∑ p ∈ Finset.univ.filter (fun p => pairCon p = c), rate p * weight h p) / Zsum h

/-- The terminal budget `U = log(1 + Ψ)` (natural logarithm). -/
noncomputable def Ubudget {ell : ℕ} {X : Fin (ell + 1) → Finset E2} {t : ℕ}
    (h : Fin t → Tag ell X × Disk) : ℝ :=
  Real.log (1 + Psi h)

/-- The boundary budget `λ_k = log(3 n_k (k+1) 2^{k+2}) + U` (Eq. (B.26)). -/
noncomputable def lamB {ell : ℕ} {X : Fin (ell + 1) → Finset E2} {t : ℕ}
    (h : Fin t → Tag ell X × Disk) (k : Fin (ell + 1)) : ℝ :=
  Real.log (3 * ((X k).card : ℝ) * ((k : ℝ) + 1) * (2 : ℝ) ^ ((k : ℕ) + 2)) + Ubudget h

/-- The centre budget `λ^ctr_0 = log 8 + U` (Eq. (B.26)). -/
noncomputable def lamCtr {ell : ℕ} {X : Fin (ell + 1) → Finset E2} {t : ℕ}
    (h : Fin t → Tag ell X × Disk) : ℝ :=
  Real.log 8 + Ubudget h

/-- A fixed Borel response selector with error `ε` (Eq. (B.12)): Borel, simplex-valued on
`Δ(C)`, and `L_κ(q(κ), g) ≤ ε` for every `κ ∈ Δ(C)` and `g ∈ B²₂`. -/
def IsResponseSelector {ell : ℕ} {X : Fin (ell + 1) → Finset E2} (ε : ℝ)
    (sel : (Con ell X → ℝ) → (Tag ell X → ℝ)) : Prop :=
  Measurable sel ∧ ∀ κ ∈ simplex (Con ell X),
    sel κ ∈ simplex (Tag ell X) ∧ ∀ g : Disk, Lkappa κ (sel κ) (g : E2) ≤ ε

/-- SHARP's response `q_t = q_{1/T}(κ_t)` after the tag–loss history `h` (Eq. (B.22)). -/
noncomputable def sharpResp {ell : ℕ} {X : Fin (ell + 1) → Finset E2}
    (sel : (Con ell X → ℝ) → (Tag ell X → ℝ)) {t : ℕ} (h : Fin t → Tag ell X × Disk) :
    Tag ell X → ℝ :=
  sel (kappa h)

end SwapDisk.Main


