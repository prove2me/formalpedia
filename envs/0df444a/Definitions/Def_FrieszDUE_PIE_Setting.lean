-- Prove2me | Definitions.Def_FrieszDUE_PIE_Setting
-- name    : FrieszDUE_PIE_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:04:40.714925+00:00
-- url     : https://prove2.me/theorems/6cbe5e10-11df-4ebb-8f81-05500531dc2f
-- title:
--   §2, §4, pp. 182–184, 187–188 — densities H₊, demand (7)–(8), Λ (38), essential infima (12)–(15), Definition 3, the VI (39), mass shift (48)–(49)
-- statement:
--   This file fixes the objects of the path-integral equilibrium (PIE) model of Friesz, Bernstein, Smith, Tobin and Wie (1993).
--
--   **Data.** A horizon $T>0$; a finite set $P$ of paths; a finite set $W$ of origin–destination (OD) pairs $kl$; a map $\mathrm{od}:P\to W$ assigning each path to the unique OD pair it connects, so that $P_{kl}=\{p : \mathrm{od}(p)=kl\}$; travel demands $Q_{kl}\in\mathbb R$; and a cost operator $C$ assigning to each path $p$, departure time $t$ and vector of densities $h$ the effective delay $C_p(t,h)$ of (13).
--
--   **The measure.** $\nu$ is Lebesgue measure on $[0,T]$. "$\forall_\nu(t)$" means "for $\nu$-almost all $t\in[0,T]$".
--
--   **Departure-time densities.** $H_+$ is the set of vectors $h=(h_p)_{p\in P}$ with every $h_p$ square-integrable on $[0,T]$ and $h_p\ge 0$ $\nu$-almost everywhere (the positive cone of $(L^2[0,T])^{|P|}$, together with the nonnegativity constraints (8)).
--
--   **Feasible set (38).**
--   $$\Lambda=\Big\{h\in H_+ : \sum_{p\in P_{kl}}\int_0^T h_p(t)\,d\nu(t)=Q_{kl}\ \text{ for all OD pairs } kl\Big\}.$$
--
--   **Essential infima (12), (14), (15).** For $F:[0,T]\to\mathbb R$,
--   $$\operatorname{ess\,inf}\{F(s): s\in[0,T]\}=\sup\{x\in\mathbb R:\ \nu\{s: F(s)<x\}=0\},$$
--   $\mu_p(h)=\operatorname{ess\,inf}\{C_p(t,h):t\in[0,T]\}$ and $\mu_{kl}(h)=\min\{\mu_p(h):p\in P_{kl}\}$.
--
--   **Definition 3 (simultaneous route-departure equilibrium).** For $h\in\Lambda$ and a nonnegative vector $\mu=(\mu_{kl})$, the pair $(h,\mu)$ is an SRD equilibrium if for every OD pair $kl$ and every $p\in P_{kl}$
--   $$h_p(t)>0\ \Rightarrow\ C_p(t,h)=\mu_{kl}\quad\forall_\nu(t),\qquad C_p(t,h)\ge\mu_{kl}\quad\forall_\nu(t).$$
--
--   **The variational inequality (39).** $h^*$ solves the PIE VI if $h^*\in\Lambda$ and
--   $$\sum_{p\in P}\int_0^T C_p(t,h^*)\,[h_p(t)-h^*_p(t)]\,d\nu(t)\ge 0\quad\text{for all } h\in\Lambda.$$
--
--   **Mass shift (48)–(49).** For paths $p\ne q$, sets $A,B$ and $\delta\in\mathbb R$, the vector $h$ with $h_p=h^*_p-\delta$ on $A$ (and $h^*_p$ elsewhere), $h_q=h^*_q+\delta$ on $B$ (and $h^*_q$ elsewhere), and $h_r=h^*_r$ for every other path $r$.
--
--   These objects are the vocabulary of Theorem 2 (PIE VIP): SRD equilibria are exactly the solutions of the VI on $\Lambda$.
--
--   **Formalization Note** Densities are plain functions $\mathbb R\to\mathbb R$ with an $L^2(\nu)$ condition rather than equivalence classes; every pointwise condition is $\nu$-a.e., as in the paper. The essential infimum is the literal formula (12) (a real supremum), not Mathlib's `essInf`. $\mu_{kl}$ is a real infimum over the paths of $P_{kl}$; for an OD pair without paths it is the junk value $0$, which no statement uses, since Definition 3 constrains $\mu_{kl}$ only through the paths of $P_{kl}$. The mass shift is defined for any $p,q$, but is used only with $p\ne q$ (the paper's reduction, p. 188).
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), pp. 182–184, 187–188, (7), (8), (12)–(17), Definition 3, (38), (39), (48), (49)

import Mathlib

namespace FrieszDUE.PIE

open MeasureTheory

/-- The paper's measure `ν`: Lebesgue measure on the analysis horizon `[0, T]` (p. 182). -/
noncomputable abbrev ν (T : ℝ) : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T)

/-- `H₊ = (L²₊[0, T])^π` together with the nonnegativity constraints (8): every path density
`h p` is square-integrable on `[0, T]` and `ν`-a.e. nonnegative (pp. 182–183). -/
def Hplus {P : Type*} (T : ℝ) : Set (P → ℝ → ℝ) :=
  {h | ∀ p, MemLp (h p) 2 (ν T) ∧ ∀ᵐ t ∂(ν T), 0 ≤ h p t}

/-- The feasible set `Λ` of (38): densities in `H₊` meeting the demand constraints (7),
`∑_{p ∈ P_kl} ∫₀ᵀ h_p dν = Q_kl` for every OD pair `kl`; here `od p = w` means `p ∈ P_w`. -/
def Lambda {P W : Type*} [Fintype P] [DecidableEq W] (T : ℝ) (od : P → W) (Q : W → ℝ) :
    Set (P → ℝ → ℝ) :=
  {h | h ∈ Hplus T ∧
    ∀ w, ∑ p ∈ Finset.univ.filter (fun p => od p = w), ∫ t, h p t ∂(ν T) = Q w}

/-- The essential infimum (12) of `F` on `S = [0, T]`:
`ess inf {F(s) : s ∈ [0, T]} = sup {x ∈ ℝ : ν{s : F(s) < x} = 0}`. -/
noncomputable def essInfOn (T : ℝ) (F : ℝ → ℝ) : ℝ :=
  sSup {x : ℝ | ν T {t | F t < x} = 0}

/-- `μ_p(h)` of (14): the essential infimum over `[0, T]` of the path cost `C_p(·, h)`. -/
noncomputable def muPath {P : Type*} (T : ℝ) (C : P → ℝ → (P → ℝ → ℝ) → ℝ)
    (h : P → ℝ → ℝ) (p : P) : ℝ :=
  essInfOn T (fun t => C p t h)

/-- `μ_kl(h)` of (15): the minimum of `μ_p(h)` over the paths `p ∈ P_kl` of the OD pair `w`. -/
noncomputable def muOD {P W : Type*} (T : ℝ) (od : P → W) (C : P → ℝ → (P → ℝ → ℝ) → ℝ)
    (h : P → ℝ → ℝ) (w : W) : ℝ :=
  ⨅ p : {p : P // od p = w}, muPath T C h p.1

/-- Definition 3: `(h, μ)` is a simultaneous route-departure (SRD) equilibrium when `h ∈ H₊`
satisfies (7) and (8) (i.e. `h ∈ Λ`), `μ` is nonnegative, and for every path `p ∈ P_kl`
(16) `h_p(t) > 0 ⇒ C_p(t, h) = μ_kl` and (17) `C_p(t, h) ≥ μ_kl` hold for `ν`-almost all `t`. -/
def IsSRDEquilibrium {P W : Type*} [Fintype P] [DecidableEq W] (T : ℝ) (od : P → W)
    (Q : W → ℝ) (C : P → ℝ → (P → ℝ → ℝ) → ℝ) (h : P → ℝ → ℝ) (mu : W → ℝ) : Prop :=
  h ∈ Lambda T od Q ∧ (∀ w, 0 ≤ mu w) ∧
    ∀ p, (∀ᵐ t ∂(ν T), 0 < h p t → C p t h = mu (od p)) ∧
      (∀ᵐ t ∂(ν T), mu (od p) ≤ C p t h)

/-- The variational inequality (39) on `Λ`: `h* ∈ Λ` and
`∑_{p ∈ P} ∫₀ᵀ C_p(t, h*) [h_p(t) − h*_p(t)] dν(t) ≥ 0` for all `h ∈ Λ`. -/
def IsPIEVISolution {P W : Type*} [Fintype P] [DecidableEq W] (T : ℝ) (od : P → W)
    (Q : W → ℝ) (C : P → ℝ → (P → ℝ → ℝ) → ℝ) (hs : P → ℝ → ℝ) : Prop :=
  hs ∈ Lambda T od Q ∧
    ∀ h ∈ Lambda T od Q, 0 ≤ ∑ p, ∫ t, C p t hs * (h p t - hs p t) ∂(ν T)

/-- The mass-shifted density vector of (48)–(49): `h_p = h*_p − δ` on `A`, `h_q = h*_q + δ` on
`B`, and `h_r = h*_r` otherwise (for `p ≠ q`). -/
noncomputable def massShift {P : Type*} [DecidableEq P] (hs : P → ℝ → ℝ) (p q : P)
    (A B : Set ℝ) (δ : ℝ) : P → ℝ → ℝ :=
  fun r t =>
    if r = p then hs p t - A.indicator (fun _ => δ) t
    else if r = q then hs q t + B.indicator (fun _ => δ) t
    else hs r t

end FrieszDUE.PIE


