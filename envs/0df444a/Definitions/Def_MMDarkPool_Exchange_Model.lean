-- Prove2me | Definitions.Def_MMDarkPool_Exchange_Model
-- name    : MMDarkPool_Exchange_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:04.556253+00:00
-- url     : https://prove2.me/theorems/9394bee9-1dae-46f5-b7fc-6e94422b325d
-- title:
--   §2.2, §4.3–§4.4, pp. 4–16 — lit/dark market-making model: intensities, MM Hamiltonian (4.10), best response (4.6), exchange Hamiltonian (4.16), viscosity solutions of (4.15)
-- statement:
--   This file sets up the market-making model of Baldacci, Manziuk, Mastrolia and Rosenbaum, in which one market maker quotes on a lit pool $l$ and a dark pool $d$ run by the same exchange, and the exchange pays the market maker incentives.
--
--   **Parameters.** A horizon $T>0$; the tick $\mathcal T>0$ (so $\mathcal T/2$ is the half tick); the volatility $\sigma>0$; the risk aversions $\gamma>0$ (market maker) and $\eta>0$ (exchange); an intensity $\epsilon>0$; for each pool $j\in\{l,d\}$ intensity parameters $A^j,\theta^j>0$, a market impact $\Gamma^j>0$ with $\Gamma^l\ge\Gamma^d$, and a fee $c^j>0$; a risk limit $\bar q\in\mathbb N$; and finite volume sets $\mathcal V^l,\mathcal V^d\subset\mathbb N$, both containing $0$. The inventory lives on the grid $\{-\bar q,\dots,\bar q\}$.
--
--   **Volumes and admissibility.** The market maker posts volumes $\ell^{i,j}\in\mathcal V^j$ on side $i\in\{a,b\}$ (ask, bid) of pool $j$. With $\phi(a)=1$, $\phi(b)=-1$, the volumes are admissible at inventory $q$ when $\ell^{i,l}+\ell^{i,d}\le 2\bar q$ for both sides and the inventory stays within the risk limits after any fill:
--   $$q-\ell^{a,l}-\ell^{a,d}\ge-\bar q,\qquad q+\ell^{b,l}+\ell^{b,d}\le\bar q.$$
--
--   **Intensities.** The lit-pool imbalances are $I^a=\ell^{a,l}/(\ell^{a,l}+\ell^{b,l})$ and $I^b=\ell^{b,l}/(\ell^{a,l}+\ell^{b,l})$, both $0$ when $\ell^{a,l}=\ell^{b,l}=0$. Let $\psi^{i,j}=I^a$ for $(i,j)\in\{(a,l),(b,d)\}$ and $\psi^{i,j}=I^b$ for $(i,j)\in\{(b,l),(a,d)\}$. Then
--   $$\lambda^{i,j}(\mathcal L^l)=A^j\exp\Big(-\frac{\theta^j}{\sigma}\psi^{i,j}(\mathcal L^l)\Big)\mathbf 1_{\{\mathcal L^l\ne(0,0)\}}+\epsilon\,\mathbf 1_{\{\mathcal L^l=(0,0)\}},\qquad \lambda^{\mathcal L,i,j,k}=\lambda^{i,j}(\mathcal L^l)\,\mathbf 1_{\{\phi(i)q>-\bar q,\ \ell^{i,j}=k\}}.$$
--   Latency is $\kappa\in K=\{\mathrm{lat},\text{non-lat}\}$, with $\phi^{\mathrm{lat}}(\mathrm{lat})=1$, $\phi^{\mathrm{lat}}(\text{non-lat})=0$, and $\phi^d(i,\kappa)=I^b$ for $(i,\kappa)\in\{(a,\mathrm{lat}),(b,\text{non-lat})\}$, $\phi^d(i,\kappa)=I^a$ otherwise.
--
--   **The market maker's Hamiltonian and best response.** For jump incentives $z=(z^{i,j,k})_{i,j,k\in\mathcal V^j}$,
--   $$h(\mathcal L,z,q)=\sum_{i\in\{a,b\}}\gamma^{-1}\Big(\sum_{k\in\mathcal V^l}\big(1-e^{-\gamma(z^{i,l,k}+\ell^{i,l}(\frac{\mathcal T}{2}+\phi(i)\Gamma^lq)-\Gamma^l(\ell^{i,l})^2)}\big)\lambda^{\mathcal L,i,l,k}+\sum_{k\in\mathcal V^d}\sum_{\kappa\in K}\big(1-e^{-\gamma(z^{i,d,k}+\ell^{i,d}(\frac{\mathcal T}{2}\phi^{\mathrm{lat}}(\kappa)+\phi(i)\Gamma^dq)-\Gamma^d(\ell^{i,d})^2)}\big)\lambda^{\mathcal L,i,d,k}\phi^d(i,\kappa)\Big).$$
--   A selection $\mathcal L^\star(z,q)$ is a best response if, for every grid point $q$ and every $z$, it is admissible at $q$ and maximizes $h(\cdot,z,q)$ over the volumes admissible at $q$.
--
--   **The exchange's Hamiltonian.** With $\mathcal E(z^{i,l,k},\ell^{i,l})=\frac1\gamma\big(1-e^{-\gamma(\cdots)}\big)$ and $\mathcal E(z^{i,d,k},\ell^{i,d})=\frac1\gamma\sum_{\kappa}\big(1-e^{-\gamma(\cdots)}\big)\phi^d(i,\kappa)$ (the same exponents as in $h$), and a row $w=v(t,\cdot)$,
--   $$\mathcal U(z,q,\mathcal L^\star,w)=w(q)\Big(\frac\eta2\sigma^2\gamma(z^{\tilde S}+q)^2+\frac{\eta^2\sigma^2}{2}(z^{\tilde S})^2\Big)+\sum_{i,j}\sum_{k\in\mathcal V^j}\lambda^{\mathcal L^\star,i,j,k}\Big(e^{\eta(z^{i,j,k}-kc^j)}w(q-\phi(i)k)-w(q)\big(1+\eta\,\mathcal E(z^{i,j,k},\ell^{\star i,j}(z,q))\big)\Big),$$
--   and $\mathcal H(q,\mathcal L^\star,w)=\sup_{(z^{\tilde S},z)}\mathcal U$, an extended real number.
--
--   **Viscosity solutions of (4.15).** $v:[0,T]\times\{-\bar q,\dots,\bar q\}\to\mathbb R$ is a continuous viscosity solution of $0=\partial_tv(t,q)+\mathcal H(q,\mathcal L^\star,v(t,\cdot))$, $v(T,q)=-1$, if for every grid point $q$: $v(\cdot,q)$ is continuous on $[0,T]$; $v(T,q)=-1$; and for every $C^1$ function $\varphi$ and every $t_0\in(0,T)$, $\varphi'(t_0)+\mathcal H(q,\mathcal L^\star,v(t_0,\cdot))\ge0$ when $v(\cdot,q)-\varphi$ has a local maximum at $t_0$, and $\le0$ when it has a local minimum there.
--
--   These objects are the data of the exchange's HJB equation (4.15)–(4.16), the subject of Theorem 3.
--
--   **Formalization Note.** Several readings are made explicit. (1) The risk limit "$2\bar q\in\mathbb N$" is read as $\bar q\in\mathbb N$, since the initial inventory $0$ lies on the grid. (2) The admissible volumes keep the inventory between $-\bar q$ and $\bar q$, as stated in §5.1.1 of the paper; this is what makes $v(t,q-\phi(i)k)$ in $\mathcal U$ a grid value whenever its coefficient is nonzero. (3) $0\in\mathcal V^l,\mathcal V^d$ is assumed, so that an admissible volume always exists. (4) The double sum over $(k^l,k^d)\in\mathcal V^l\times\mathcal V^d$ printed in (4.10) counts the lit terms $\#\mathcal V^d$ times and the dark terms $\#\mathcal V^l$ times; it is read as one sum per pool, as in $\mathcal U$. (5) The paper does not spell out its viscosity notion; the standard per-component notion for a finite system of backward ODEs is used, with interior test times and the solution's own row $v(t_0,\cdot)$ as the nonlocal argument. (6) $\mathcal H$ is a supremum in `EReal` because it can be $+\infty$. Inventories are integers, cast to reals in the formulas. Remark 2.2's informal requirement that the impacts be small with respect to the tick, and "$\epsilon$ small enough", are not encoded.
-- source:
--   Baldacci, Manziuk, Mastrolia & Rosenbaum, arXiv:1912.01129v1, pp. 4–7 (§2.1–§2.2, A, ψ, λ, footnote 5, Γ, tick, Remark 2.2), p. 8 (K, φ^lat, φ^d), p. 9 (fees c^j), p. 10 ((4.6)), p. 11 ((4.10)), p. 13 (𝓔, (4.15)), p. 14 ((4.16), 𝓤), p. 16 (§5.1.1 risk limits)

import Mathlib

namespace MMDarkPool.Exchange

/-!
# Lit/dark market-making model with an exchange (Baldacci–Manziuk–Mastrolia–Rosenbaum)

Source: B. Baldacci, I. Manziuk, T. Mastrolia, M. Rosenbaum, *Market making and incentives design in
the presence of a dark pool: a deep reinforcement learning approach*, arXiv:1912.01129v1:
§2.2 (pp. 4–7), K, φ^lat, φ^d (p. 8), (4.6) (p. 10), (4.10) (p. 11), 𝓔 and (4.15) (p. 13),
(4.16) and 𝓤 (p. 14), risk limits (§5.1.1, p. 16).

Readings fixed here (disclosed):
* the risk limit `2q̄ ∈ ℕ` (p. 4) is read as `q̄ ∈ ℕ`, since the initial inventory `Q₀ = 0` lies on the
  grid `{−q̄, …, q̄}`;
* the admissible volumes at inventory `q` keep the inventory within the risk limits
  (§5.1.1, p. 16): `q − ℓ^{a,l} − ℓ^{a,d} ≥ −q̄` and `q + ℓ^{b,l} + ℓ^{b,d} ≤ q̄`, besides the
  constraint `ℓ^{i,l} + ℓ^{i,d} ∈ [0, 2q̄]` of 𝒜 (p. 5);
* `0 ∈ V^l` and `0 ∈ V^d` (posting nothing is always possible);
* the double sum over `(k^l, k^d) ∈ V^l × V^d` in (4.10) is read as one sum over `k ∈ V^l` for
  the lit terms and one over `k ∈ V^d` for the dark terms, as in 𝓤 (4.16);
* the imbalances follow footnote 5: `I^a(0,0) = I^b(0,0) = 0`;
* 𝓗 (4.16) is a supremum in `EReal`, since it can be `+∞`;
* the paper does not state its viscosity notion; the standard per-component notion for a finite
  system of backward ODEs is used: `C¹` test functions in `t`, interior test times `t₀ ∈ (0, T)`,
  the nonlocal argument is the solution's own row `v(t₀, ·)`, subsolution `∂ₜφ + 𝓗 ≥ 0` at a local
  maximum of `v(·, q) − φ`, supersolution `∂ₜφ + 𝓗 ≤ 0` at a local minimum, together with continuity
  on `[0, T]` and the terminal condition `v(T, q) = −1`.
-/

/-- The two sides of the book: ask `a` and bid `b`. -/
inductive Side
  | a
  | b
  deriving DecidableEq

instance : Fintype Side where
  elems := {Side.a, Side.b}
  complete := fun x => by cases x <;> simp

/-- The two pools: lit `l` and dark `d`. -/
inductive Pool
  | l
  | d
  deriving DecidableEq

instance : Fintype Pool where
  elems := {Pool.l, Pool.d}
  complete := fun x => by cases x <;> simp

/-- The latency states `K = {lat, non-lat}` (p. 8). -/
inductive Lat
  | lat
  | nonlat
  deriving DecidableEq

instance : Fintype Lat where
  elems := {Lat.lat, Lat.nonlat}
  complete := fun x => by cases x <;> simp

/-- Model parameters. `T` is the horizon; `tick` is the tick `𝓣` (so `𝓣/2` is the half tick);
`σ` the volatility, `γ` the market maker's and `η` the exchange's risk aversion, `ε` the intensity
when nothing is posted in the lit pool, `A j`, `θ j` the intensity parameters, `Γ j` the impacts,
`c j` the exchange fees, `qbar` the risk limit `q̄`, and `V j` the finite volume sets `V^l`, `V^d`. -/
structure Params where
  T : ℝ
  tick : ℝ
  σ : ℝ
  γ : ℝ
  η : ℝ
  ε : ℝ
  A : Pool → ℝ
  θ : Pool → ℝ
  Γ : Pool → ℝ
  c : Pool → ℝ
  qbar : ℕ
  V : Pool → Finset ℕ

/-- The standing assumptions of §2 (pp. 4–7), Remark 2.2 and p. 9, plus `0 ∈ V^l, V^d`. -/
def Standing (P : Params) : Prop :=
  0 < P.T ∧ 0 < P.tick ∧ 0 < P.σ ∧ 0 < P.γ ∧ 0 < P.η ∧ 0 < P.ε ∧
  (∀ j, 0 < P.A j ∧ 0 < P.θ j) ∧ (∀ j, 0 < P.Γ j) ∧ P.Γ Pool.d ≤ P.Γ Pool.l ∧
  (∀ j, 0 < P.c j) ∧ (∀ j, 0 ∈ P.V j)

/-- The inventory grid `{−q̄, …, q̄}`. -/
def Grid (P : Params) : Set ℤ := {q | -(P.qbar : ℤ) ≤ q ∧ q ≤ (P.qbar : ℤ)}

/-- `φ(i) = 1` for `i = a`, `−1` for `i = b` (p. 5). -/
def phiSide : Side → ℤ
  | Side.a => 1
  | Side.b => -1

/-- Volumes `ℓ^{i,j}` posted on side `i` of pool `j`. -/
abbrev Vol := Side → Pool → ℕ

/-- Volumes admissible at inventory `q`: each `ℓ^{i,j} ∈ V^j`, `ℓ^{i,l} + ℓ^{i,d} ≤ 2q̄` (𝒜, p. 5),
and the inventory stays within the risk limits after any fill (§5.1.1, p. 16). -/
def Admissible (P : Params) (q : ℤ) (L : Vol) : Prop :=
  (∀ i j, L i j ∈ P.V j) ∧ (∀ i, L i Pool.l + L i Pool.d ≤ 2 * P.qbar) ∧
  -(P.qbar : ℤ) ≤ q - (L Side.a Pool.l : ℤ) - (L Side.a Pool.d : ℤ) ∧
  q + (L Side.b Pool.l : ℤ) + (L Side.b Pool.d : ℤ) ≤ (P.qbar : ℤ)

/-- Ask imbalance of the lit pool `I^a = ℓ^{a,l}/(ℓ^{a,l} + ℓ^{b,l})`, with `I^a(0,0) = 0`
(footnote 5). -/
noncomputable def Ia (L : Vol) : ℝ :=
  if L Side.a Pool.l + L Side.b Pool.l = 0 then 0
  else (L Side.a Pool.l : ℝ) / ((L Side.a Pool.l : ℝ) + (L Side.b Pool.l : ℝ))

/-- Bid imbalance of the lit pool `I^b = ℓ^{b,l}/(ℓ^{a,l} + ℓ^{b,l})`, with `I^b(0,0) = 0`
(footnote 5). -/
noncomputable def Ib (L : Vol) : ℝ :=
  if L Side.a Pool.l + L Side.b Pool.l = 0 then 0
  else (L Side.b Pool.l : ℝ) / ((L Side.a Pool.l : ℝ) + (L Side.b Pool.l : ℝ))

/-- `ψ^{i,j}` (p. 5): `I^a` for `(a,l)`, `(b,d)`; `I^b` for `(b,l)`, `(a,d)`. -/
noncomputable def psi : Side → Pool → Vol → ℝ
  | Side.a, Pool.l, L => Ia L
  | Side.b, Pool.d, L => Ia L
  | Side.b, Pool.l, L => Ib L
  | Side.a, Pool.d, L => Ib L

/-- `λ^{i,j}(𝓛^l) = A^j exp(−(θ^j/σ) ψ^{i,j}(𝓛^l)) 1{𝓛^l ≠ (0,0)} + ε 1{𝓛^l = (0,0)}` (p. 5). -/
noncomputable def lam (P : Params) (i : Side) (j : Pool) (L : Vol) : ℝ :=
  if L Side.a Pool.l = 0 ∧ L Side.b Pool.l = 0 then P.ε
  else P.A j * Real.exp (-(P.θ j / P.σ) * psi i j L)

/-- `λ^{𝓛,i,j,k} = λ^{i,j}(𝓛^l) 1{φ(i) q > −q̄, ℓ^{i,j} = k}` at inventory `q` (p. 5). -/
noncomputable def lamK (P : Params) (q : ℤ) (i : Side) (j : Pool) (k : ℕ) (L : Vol) : ℝ :=
  if phiSide i * q > -(P.qbar : ℤ) ∧ L i j = k then lam P i j L else 0

/-- `φ^lat(lat) = 1`, `φ^lat(non-lat) = 0` (p. 8). -/
def phiLat : Lat → ℝ
  | Lat.lat => 1
  | Lat.nonlat => 0

/-- `φ^d(i, κ)` (p. 8): `I^b` for `(a, lat)`, `(b, non-lat)`; `I^a` for `(a, non-lat)`, `(b, lat)`. -/
noncomputable def phiD : Side → Lat → Vol → ℝ
  | Side.a, Lat.lat, L => Ib L
  | Side.b, Lat.nonlat, L => Ib L
  | Side.a, Lat.nonlat, L => Ia L
  | Side.b, Lat.lat, L => Ia L

/-- Jump incentives `z = (z^{i,j,k})_{i ∈ {a,b}, j ∈ {l,d}, k ∈ V^j} ∈ ℝ^{2(#V^l+#V^d)}`. -/
abbrev Inc (P : Params) := (i : Side) → (j : Pool) → {k : ℕ // k ∈ P.V j} → ℝ

/-- Lit-pool exponent `z^{i,l,k} + ℓ^{i,l}(𝓣/2 + φ(i)Γ^l q) − Γ^l(ℓ^{i,l})²` ((4.10), 𝓔). -/
noncomputable def litGain (P : Params) (L : Vol) (zk : ℝ) (q : ℤ) (i : Side) : ℝ :=
  zk + (L i Pool.l : ℝ) * (P.tick / 2 + (phiSide i : ℝ) * P.Γ Pool.l * (q : ℝ))
    - P.Γ Pool.l * (L i Pool.l : ℝ) ^ 2

/-- Dark-pool exponent `z^{i,d,k} + ℓ^{i,d}(𝓣/2 φ^lat(κ) + φ(i)Γ^d q) − Γ^d(ℓ^{i,d})²`
((4.10), 𝓔). -/
noncomputable def darkGain (P : Params) (L : Vol) (zk : ℝ) (q : ℤ) (i : Side) (κ : Lat) : ℝ :=
  zk + (L i Pool.d : ℝ) * (P.tick / 2 * phiLat κ + (phiSide i : ℝ) * P.Γ Pool.d * (q : ℝ))
    - P.Γ Pool.d * (L i Pool.d : ℝ) ^ 2

/-- The market maker's Hamiltonian `h(𝓛, z, q)` of (4.10), with each process `N^{i,j,k}` counted
once (lit terms summed over `k ∈ V^l`, dark terms over `k ∈ V^d`). -/
noncomputable def hMM (P : Params) (L : Vol) (z : Inc P) (q : ℤ) : ℝ :=
  ∑ i : Side, P.γ⁻¹ *
    ((∑ k : {k : ℕ // k ∈ P.V Pool.l},
        (1 - Real.exp (-P.γ * litGain P L (z i Pool.l k) q i)) * lamK P q i Pool.l k.1 L) +
      ∑ k : {k : ℕ // k ∈ P.V Pool.d}, ∑ κ : Lat,
        (1 - Real.exp (-P.γ * darkGain P L (z i Pool.d k) q i κ)) * lamK P q i Pool.d k.1 L *
          phiD i κ L)

/-- `Lstar` is an optimal response of the market maker in the sense of (4.6): for every inventory
`q` on the grid and every jump incentive `z`, `Lstar z q` is admissible at `q` and maximizes
`h(·, z, q)` over the volumes admissible at `q`. -/
def IsBestResponse (P : Params) (Lstar : Inc P → ℤ → Vol) : Prop :=
  ∀ q ∈ Grid P, ∀ z : Inc P,
    Admissible P q (Lstar z q) ∧ ∀ L : Vol, Admissible P q L → hMM P L z q ≤ hMM P (Lstar z q) z q

/-- `𝓔(z^{i,j,k}, ℓ^{i,j})` (p. 13): `(1/γ)(1 − exp(−γ · litGain))` for `j = l`, and
`(1/γ) Σ_κ (1 − exp(−γ · darkGain)) φ^d(i, κ)` for `j = d`. -/
noncomputable def Ecal (P : Params) (L : Vol) (i : Side) (j : Pool) (zk : ℝ) (q : ℤ) : ℝ :=
  match j with
  | Pool.l => (1 / P.γ) * (1 - Real.exp (-P.γ * litGain P L zk q i))
  | Pool.d => (1 / P.γ) * ∑ κ : Lat,
      (1 - Real.exp (-P.γ * darkGain P L zk q i κ)) * phiD i κ L

/-- `𝓤(z, q, 𝓛⋆(z, q), w)` of (4.16) (p. 14), for the full incentive `x = (z^S̃, z)` and a row
`w = v(t, ·)`:
`w(q)((η/2)σ²γ(z^S̃ + q)² + (η²σ²/2)(z^S̃)²)
  + Σ_{i,j} Σ_{k ∈ V^j} λ^{𝓛⋆,i,j,k}(exp(η(z^{i,j,k} − k c^j)) w(q − φ(i)k) − w(q)(1 + η 𝓔))`. -/
noncomputable def Ucal (P : Params) (Lstar : Inc P → ℤ → Vol) (x : ℝ × Inc P) (q : ℤ)
    (w : ℤ → ℝ) : ℝ :=
  w q * ((P.η / 2) * P.σ ^ 2 * P.γ * (x.1 + (q : ℝ)) ^ 2 + (P.η ^ 2 * P.σ ^ 2 / 2) * x.1 ^ 2) +
    ∑ i : Side, ∑ j : Pool, ∑ k : {k : ℕ // k ∈ P.V j},
      lamK P q i j k.1 (Lstar x.2 q) *
        (Real.exp (P.η * (x.2 i j k - (k.1 : ℝ) * P.c j)) * w (q - phiSide i * (k.1 : ℤ)) -
          w q * (1 + P.η * Ecal P (Lstar x.2 q) i j (x.2 i j k) q))

/-- The exchange's Hamiltonian `𝓗(q, 𝓛⋆, w) = sup_{z ∈ ℝ^{2(#V^l+#V^d)+1}} 𝓤` of (4.16), as an
extended real (it may be `+∞`). -/
noncomputable def Hcal (P : Params) (Lstar : Inc P → ℤ → Vol) (q : ℤ) (w : ℤ → ℝ) : EReal :=
  ⨆ x : ℝ × Inc P, ((Ucal P Lstar x q w : ℝ) : EReal)

/-- `v` is a continuous viscosity solution of (4.15) on `[0, T] × {−q̄, …, q̄}`:
`0 = ∂ₜ v(t, q) + 𝓗(q, 𝓛⋆, v(t, ·))`, `v(T, q) = −1`. For every grid point `q`: `v(·, q)` is
continuous on `[0, T]`, `v(T, q) = −1`, and for every `C¹` test function `φ` and interior time
`t₀ ∈ (0, T)`, `∂ₜφ(t₀) + 𝓗(q, 𝓛⋆, v(t₀, ·)) ≥ 0` if `v(·, q) − φ` has a local maximum at `t₀`
(subsolution) and `≤ 0` if it has a local minimum there (supersolution). -/
def IsViscositySolution (P : Params) (Lstar : Inc P → ℤ → Vol) (v : ℝ → ℤ → ℝ) : Prop :=
  ∀ q ∈ Grid P,
    ContinuousOn (fun t => v t q) (Set.Icc 0 P.T) ∧ v P.T q = -1 ∧
    (∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → ∀ t₀ ∈ Set.Ioo 0 P.T,
      IsLocalMax (fun t => v t q - φ t) t₀ →
        0 ≤ ((deriv φ t₀ : ℝ) : EReal) + Hcal P Lstar q (v t₀)) ∧
    (∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → ∀ t₀ ∈ Set.Ioo 0 P.T,
      IsLocalMin (fun t => v t q - φ t) t₀ →
        ((deriv φ t₀ : ℝ) : EReal) + Hcal P Lstar q (v t₀) ≤ 0)

end MMDarkPool.Exchange


