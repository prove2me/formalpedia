-- Prove2me | Definitions.Def_MMDarkPool_Exchange_Supplement_Model
-- name    : MMDarkPool_Exchange_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:22:12.972217+00:00
-- url     : https://prove2.me/theorems/3544eedd-9bc8-4eb0-b404-cd14b3e9d149
-- title:
--   §2–§3, pp. 4–8 — real-volume market-maker Hamiltonian and HJB equation (3.2)
-- statement:
--   Let $i\in\{a,b\}$ denote ask and bid, $j\in\{l,d\}$ the lit and dark pools, and $K=\{\mathrm{lat},\mathrm{nonlat}\}$. Reuse these finite types and $\phi(a)=1$, $\phi(b)=-1$, $\phi^{\mathrm{lat}}(\mathrm{lat})=1$, $\phi^{\mathrm{lat}}(\mathrm{nonlat})=0$ from the published model. Parameters are horizon $T$, tick $\mathcal T$, volatility $\sigma$, risk aversion $\gamma$, zero-posting intensity $\epsilon$, pool parameters $A^j,\theta^j,\Gamma^j$, a real risk limit $\bar q$, and finite sets $\mathcal V^j\subset\mathbb N$. Standing assumptions require all these numerical parameters except $\bar q$ to be positive, $\Gamma^d\le\Gamma^l$, and $2\bar q\in\mathbb N$. The volume sets may be empty and need not contain zero.
--
--   A control $L=(\ell^{i,j})$ ranges over the whole real box $O=[0,2\bar q]^4$. Set $I^a=\ell^{a,l}/(\ell^{a,l}+\ell^{b,l})$, $I^b=\ell^{b,l}/(\ell^{a,l}+\ell^{b,l})$, both zero at zero lit posting. Set $\psi^{a,l}=\psi^{b,d}=I^a$ and $\psi^{b,l}=\psi^{a,d}=I^b$. The base intensity is $\lambda^{i,j}=A^j e^{-(\theta^j/\sigma)\psi^{i,j}}$ unless both lit volumes vanish, when it is $\epsilon$. For inventory $q\in\mathbb Z$ and size $k\in\mathcal V^j$, set $\lambda^{L,i,j,k}=\lambda^{i,j}\mathbf1_{\{\phi(i)q>-\bar q,\ \ell^{i,j}=k\}}$. Dark weights are $\phi^d(a,\mathrm{lat})=\phi^d(b,\mathrm{nonlat})=I^b$, with $I^a$ in the other two cases.
--
--   For a row $w:\mathbb Z\to\mathbb R$, define $J(L,q,w)$ by
--   $$
--   \begin{aligned}
--   J(L,q,w)={}&\sum_i\sum_{k\in\mathcal V^l}\lambda^{L,i,l,k}\left[e^{-\gamma\ell^{i,l}(\mathcal T/2+\Gamma^l(\phi(i)q-\ell^{i,l}))}w(q-\phi(i)k)-w(q)\right]\\
--   &+\sum_i\sum_{\kappa\in K}\sum_{k\in\mathcal V^d}\lambda^{L,i,d,k}\phi^d(i,\kappa)\left[e^{-\gamma\ell^{i,d}(\mathcal T\phi^{\mathrm{lat}}(\kappa)/2+\Gamma^d(\phi(i)q-\ell^{i,d}))}w(q-\phi(i)k)-w(q)\right],\\
--   F(q,w)={}&\tfrac12\sigma^2\gamma^2q^2w(q)+\sup_{L\in O}J(L,q,w).
--   \end{aligned}
--   $$
--   A viscosity solution is a solution of $\partial_t v+F(q,v(t,\cdot))=0$ with $v(T,q)=-1$ for every integer $q$, in the separately defined per-component backward viscosity sense.
--
--   These definitions supply the literal real-volume Hamiltonian for the first assertion of Theorem 1. They do not identify this equation with the stochastic value function.
--
--   **Formalization Note.** Only the finite side, pool and latency types and the two scalar sign/latency functions are reused from the base model. Its natural-volume parameters, grid, standing predicate, admissibility and Hamiltonians are not reused. The real box has no constraint on the sum of the two pool volumes on one side and no prohibition of inventory overshoots. A posted volume outside $\mathcal V^j$ simply has zero size-specific intensity. Inventory is integer-valued and is cast to reals in inequalities and gains. The supremum is in `EReal`, the sums count each pool once, and the equation is imposed on all integer rows. The paper leaves the viscosity notion implicit; tests use the solution's own row at interior times, as specified in BackwardViscosity. Informal smallness conditions on $\epsilon$ and the impacts are omitted.
--
--   Differences from the source:
--   - reading: The domain of q in (3.2) is not specified; the jumps use q − φ(i)k. → The equation and uniqueness are posed on [0,T] × ℤ.; reason: Q is integer-valued by §2.2.1; all jump destinations then belong to the equation domain. No grid extension is left arbitrary.
--   - reading: The printed sum in (3.2) runs over Vˡ × Vᵈ, repeating the pool-specific terms. → One sum over Vˡ for lit fills and one over Vᵈ for dark fills.; reason: Each counting process contributes once, consistently with the single-counting reading of the published base model and the per-process sum in (4.16).
--   - reading: Theorem 1 says viscosity solution without defining the notion. → Componentwise C¹ tests at interior times, backward signs ≥ 0 at maxima and ≤ 0 at minima, and coupling evaluated on v(t,·). Continuity and terminal data are required.; reason: This fixes the time-only solution notion, using the published base convention without importing its grid.
--   - generalization: ε is called small enough (p. 4), and Γˡ, Γᵈ small relative to the tick (Remark 2.2). → All positive ε and impacts Γˡ ≥ Γᵈ > 0 are allowed, with no smallness premise.; reason: The paper gives no thresholds. The bounded-control, finite-range Lipschitz Hamiltonian is well posed for every such fixed parameter tuple; see MODERATION_NOTES.md.
--   - encoding: A supremum of real jump payoffs over O is used in (3.2). → The supremum and risk term are combined in EReal; all solution values remain real.; reason: This preserves the mathematical supremum even before boundedness is proved and avoids the default value of an unbounded real supremum.
-- source:
--   Baldacci, Manziuk, Mastrolia & Rosenbaum, arXiv:1912.01129v1, pp. 4–7, §2.1–§2.2, Remark 2.2 and footnote 5; p. 8, HJB (3.2), O, K, φ^lat, φ^d and terminal condition.

import Mathlib
import Definitions.Def_MMDarkPool_Exchange_Model
import Definitions.Def_MMDarkPool_Exchange_Supplement_BackwardViscosity

namespace MMDarkPool.Exchange.Supplement

/-!
The market maker's HJB equation (3.2), arXiv:1912.01129v1, pp. 4–8.

Only the published Side, Pool, Lat, phiSide and phiLat are reused.
The posted volumes in O are real, qbar is real with `2*qbar ∈ ℕ`, and V
need not contain zero. The published Standing, Vol and Grid are not used.
The supremum is over exactly O = [0,2*qbar]^4, without the sum constraint
of the stochastic controls A or inventory-preserving constraints.

Readings: one sum per pool in (3.2); inventory ranges over all ℤ so jumps
are closed; per-component viscosity tests at interior times as defined in
BackwardViscosity, using the solution's own row and the backward signs.
The informal smallness requirements on ε and Γ are not hypotheses.
The supremum is in EReal. At each fixed q and real row w the family is
nonempty and bounded under Standing (not an assumption in the theorem).
-/

/-- The parameters that occur in (3.2), with literal real risk limit q̄. -/
structure Params where
  T : ℝ
  tick : ℝ
  σ : ℝ
  γ : ℝ
  ε : ℝ
  A : Pool → ℝ
  θ : Pool → ℝ
  Γ : Pool → ℝ
  qbar : ℝ
  V : Pool → Finset ℕ

/-- Standing numerical assumptions from pp. 4–7 and Remark 2.2.
`∃ n : ℕ, 2*qbar = n` retains half-integer risk limits, including zero. -/
def Standing (P : Params) : Prop :=
  0 < P.T ∧ 0 < P.tick ∧ 0 < P.σ ∧ 0 < P.γ ∧ 0 < P.ε ∧
  (∀ j, 0 < P.A j ∧ 0 < P.θ j) ∧ (∀ j, 0 < P.Γ j) ∧
  P.Γ Pool.d ≤ P.Γ Pool.l ∧ ∃ n : ℕ, 2 * P.qbar = (n : ℝ)

/-- The four posted volumes, real as in O on p. 8. -/
abbrev Vol := Side → Pool → ℝ

/-- O = [0,2q̄]^4. In particular there is no per-side sum constraint. -/
def Controls (P : Params) : Set Vol :=
  {L | ∀ i j, L i j ∈ Set.Icc 0 (2 * P.qbar)}

/-- Iᵃ at real posted volumes; the zero-denominator value is footnote 5. -/
noncomputable def Ia (L : Vol) : ℝ :=
  if L Side.a Pool.l + L Side.b Pool.l = 0 then 0
  else L Side.a Pool.l / (L Side.a Pool.l + L Side.b Pool.l)

/-- Iᵇ at real posted volumes; the zero-denominator value is footnote 5. -/
noncomputable def Ib (L : Vol) : ℝ :=
  if L Side.a Pool.l + L Side.b Pool.l = 0 then 0
  else L Side.b Pool.l / (L Side.a Pool.l + L Side.b Pool.l)

/-- ψ of §2.2.1, p. 5. -/
noncomputable def psi : Side → Pool → Vol → ℝ
  | Side.a, Pool.l, L => Ia L
  | Side.b, Pool.d, L => Ia L
  | Side.b, Pool.l, L => Ib L
  | Side.a, Pool.d, L => Ib L

/-- Baseline fill rate, p. 5; zero lit posting gives ε. -/
noncomputable def lam (P : Params) (i : Side) (j : Pool) (L : Vol) : ℝ :=
  if L Side.a Pool.l = 0 ∧ L Side.b Pool.l = 0 then P.ε
  else P.A j * Real.exp (-(P.θ j / P.σ) * psi i j L)

/-- Size-k fill rate with the strict inventory indicator of p. 5.
The integer inventory and natural trade size are cast to reals only here. -/
noncomputable def lamK (P : Params) (q : ℤ) (i : Side) (j : Pool)
    (k : ℕ) (L : Vol) : ℝ :=
  if (phiSide i : ℝ) * (q : ℝ) > -P.qbar ∧ L i j = (k : ℝ)
  then lam P i j L else 0

/-- The dark latency weights in (3.2), p. 8. -/
noncomputable def phiD : Side → Lat → Vol → ℝ
  | Side.a, Lat.lat, L => Ib L
  | Side.b, Lat.nonlat, L => Ib L
  | Side.a, Lat.nonlat, L => Ia L
  | Side.b, Lat.lat, L => Ia L

/-- The lit gain inside the exponential of (3.2). -/
noncomputable def litGain (P : Params) (L : Vol) (q : ℤ) (i : Side) : ℝ :=
  L i Pool.l * (P.tick / 2 + P.Γ Pool.l * ((phiSide i : ℝ) * (q : ℝ) - L i Pool.l))

/-- The dark gain inside the exponential of (3.2). -/
noncomputable def darkGain (P : Params) (L : Vol) (q : ℤ) (i : Side) (κ : Lat) : ℝ :=
  L i Pool.d *
    (P.tick / 2 * phiLat κ + P.Γ Pool.d * ((phiSide i : ℝ) * (q : ℝ) - L i Pool.d))

/-- The controlled jump expression in (3.2), counting each size once per pool. -/
noncomputable def jumpHamiltonian (P : Params) (L : Vol) (q : ℤ) (w : ℤ → ℝ) : ℝ :=
  (∑ i : Side, ∑ k ∈ P.V Pool.l,
    lamK P q i Pool.l k L *
      (Real.exp (-P.γ * litGain P L q i) * w (q - phiSide i * (k : ℤ)) - w q)) +
  ∑ i : Side, ∑ κ : Lat, ∑ k ∈ P.V Pool.d,
    lamK P q i Pool.d k L * phiD i κ L *
      (Real.exp (-P.γ * darkGain P L q i κ) * w (q - phiSide i * (k : ℤ)) - w q)

/-- F(q,w) of `0 = ∂ₜv + F(q,v(t,·))`, including the γ² inventory-risk term.
Subtype indexing takes exactly the supremum over O, with no junk real supremum. -/
noncomputable def F (P : Params) (q : ℤ) (w : ℤ → ℝ) : EReal :=
  ((w q * (1 / 2 : ℝ) * P.σ ^ 2 * P.γ ^ 2 * (q : ℝ) ^ 2 : ℝ) : EReal) +
    ⨆ L : {L : Vol // L ∈ Controls P}, ((jumpHamiltonian P L.1 q w : ℝ) : EReal)

/-- Viscosity solution of (3.2) for every q ∈ ℤ, with terminal value −1. -/
def IsViscositySolution (P : Params) (v : ℝ → ℤ → ℝ) : Prop :=
  IsBackwardViscositySolution P.T (F P) (fun _ => -1) v

end MMDarkPool.Exchange.Supplement


