-- Prove2me | Definitions.Def_FairRentFPTAS_Approx_Model
-- name    : FairRentFPTAS_Approx_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:23.459737+00:00
-- url     : https://prove2.me/theorems/5fd21ca7-465d-437d-b1a3-a45b3f34926a
-- title:
--   §2, §4, §5 — piecewise-linear rent-division instances, EF and ε-EF (Def. 2), linear domains (Def. 1), F_w(p), Algorithm 1 runs with (1), slope rounding Ī
-- statement:
--   This file fixes the model of fair rent division with piecewise-linear utilities and the objects of Algorithm 1 and of the slope rounding of §5.
--
--   1. **Utilities.** A utility function $v(\cdot)$ of the rent is given by its base value $v(0)$, break points $0=b_1<b_2<\dots<b_t$ and slope magnitudes $\lambda_1,\dots,\lambda_t>0$; on $[b_i,b_{i+1}]$ (the last piece unbounded)
--   $$v(x)=v(0)-\sum_{j=1}^{i-1}\lambda_j(b_{j+1}-b_j)-\lambda_i(x-b_i).$$
--   Such a function is continuous and strictly decreasing. The **left slope** at $x$ is the slope of the piece to the left of $x$.
--   2. **Instances and solutions.** An instance has $n$ agents and $n$ rooms, agent $a$'s utility for room $r$ being $v_a(r,\cdot)$; $\ell$ is the total number of pieces. A solution $(\pi,p)$ is a bijection $\pi$ (agent $a$ gets room $\pi(a)$) and a rent vector $p\in\mathbb R^n$. It is **envy-free** if $v_a(\pi(a),p_{\pi(a)})\ge v_a(r,p_r)$ for all $a,r$, and **$\varepsilon$-EF** (Definition 2) if every agent with $v_a(\pi(a),p_{\pi(a)})\ge 0$ satisfies $(1+\varepsilon)v_a(\pi(a),p_{\pi(a)})\ge v_a(r,p_r)$ for all $r$, and every agent with $v_a(\pi(a),p_{\pi(a)})<0$ satisfies $v_a(\pi(a),p_{\pi(a)})\ge(1+\varepsilon)v_a(r,p_r)$ for all $r$.
--   3. **First-choice graph, weights, linear domain.** $(a,r)$ is a first-choice edge at $p$ if $v_a(r,p_r)\ge v_a(r',p_{r'})$ for all $r'$. The weight of an assignment $\sigma$ is $w(\sigma)=\sum_a\log\lambda^a_{\sigma(a)}$, with $\lambda^a_r$ the left slope of $v_a(r,\cdot)$ at $p_r$; a maximum-weight perfect matching of $\mathcal F^w(p)$ is an assignment using only first-choice edges whose weight is maximal among such assignments. The linear domain $(L,U)$ of $p$ (Definition 1) has, for each room, $L_r$ the largest and $U_r$ the smallest boundary point with $L_r<p_r\le U_r$, the boundary points of room $r$ being the price $0$ and the break points at which some $v_a(r,\cdot)$ changes slope ($L_r=-\infty$, $U_r=+\infty$ if none).
--   4. **Algorithm 1.** For a threshold $M$ with $v_a(r,M)<v_a(r',0)$ for all $a,r,r'$, equation (1) defines $\hat v_a(r,x)=v_a(r,x)$ for $x\le M$ and $\hat v_a(r,x)=v_a(r,M)-(x-M)$ for $x>M$, giving the instance $\hat{\mathcal I}$. A run of length $T$ is a sequence $(\pi^0,p^0),\dots,(\pi^T,p^T)$ where $(\pi^0,p^0)$ is an envy-free solution of $\hat{\mathcal I}$ with $p^0\ge M\mathbb 1$, and for each $i<T$: all $p^i_r>0$, $\pi^{i+1}$ is a maximum-weight perfect matching of $\mathcal F^w(p^i)$ for $\hat{\mathcal I}$, and $p^{i+1}$ is an optimal solution of
--   $$\min_{x\in\mathbb R^n}\sum_r x_r\quad\text{s.t. } U^i\ge x\ge L^i,\ \ \hat v_a(\pi^{i+1}(a),x_{\pi^{i+1}(a)})\ge\hat v_a(r,x_r)\ \forall a,r,\ \ x\ge 0,$$
--   with $(L^i,U^i)$ the linear domain of $p^i$. The run has halted when some $p^T_r\le 0$.
--   5. **Slope rounding (§5).** For $\varepsilon>0$ and a slope $\lambda$, $\bar\lambda=(1+\varepsilon)^{\lceil\log_{1+\varepsilon}\lambda\rceil}$. To build $\bar v_a(r,\cdot)$, the zero $z^a_r$ of $v_a(r,\cdot)$ is first made a break point; then each bounded piece $[x_1,x_2]$ of slope $\lambda$ is replaced by a piece of slope $\bar\lambda/(1+\varepsilon)$ on $[x_1,x^*)$ and one of slope $\bar\lambda$ on $[x^*,x_2]$, where
--   $$x^*=x_1+\frac{(1+\varepsilon)(\bar\lambda-\lambda)(x_2-x_1)}{\varepsilon\bar\lambda}$$
--   solves $v(x_1)=v(x_2)+\bar\lambda(x_2-x^*)+\frac{\bar\lambda}{1+\varepsilon}(x^*-x_1)$. The unbounded last piece gets slope $\bar\lambda/(1+\varepsilon)$. The result is the instance $\bar{\mathcal I}$. An instance has the powers-of-$(1+\varepsilon)$ property if every slope is $(1+\varepsilon)^k$ with $k\in\mathbb Z$.
--
--   These objects are shared by every statement of the mission: Theorem 2 is about runs of Algorithm 1 on $\bar{\mathcal I}$.
--
--   **Formalization Note** A utility is a `PLFun` (base value and a list of `(start, slope)` pairs); `Standing I` says every utility is well formed (first start $0$, strictly increasing starts, positive slopes). Agents and rooms are `Fin n`, allocations `Equiv.Perm (Fin n)`. For negative rents, which only Lemma 2 uses, the first piece is extended linearly. The price $0$ is added to the boundary points of the linear domains (the paper treats $b_1=0$ as a break point), and break points across which no slope changes are not boundaries, as Definition 1's maximality requires. The paper writes the rounding only for bounded pieces; rounding the unbounded last piece down to $\bar\lambda/(1+\varepsilon)$ is this formalization's convention (after the zero split that piece has nonpositive utility). Algorithm choices (Step 2's solution, the matching, the LP optimum) are arbitrary, so a run is a predicate on sequences.
-- source:
--   Arunachaleswaran, Barman & Rathi, Fully Polynomial-Time Approximation Schemes for Fair Rent Division, arXiv:1807.04163v1, pp. 6–8, 10–11, 16, §2, Definitions 1–2, (1), Algorithm 1, (5)

import Mathlib

namespace FairRentFPTAS.Approx

/-! # Fair rent division with piecewise-linear utilities (Arunachaleswaran, Barman & Rathi,
arXiv:1807.04163v1, §2 pp. 6–8, §4 pp. 10–11, §5 p. 16). -/

/-- A continuous piecewise-linear utility function of the price, given by its base value
`v(0)` and its linear pieces. Each entry `(start, slope)` of `pieces` is one piece: it begins
at `start` and runs to the next entry's `start`; the last piece is unbounded. On a piece the
function decreases with rate `slope` (the paper's slope magnitude `λ`). -/
structure PLFun where
  base : ℝ
  pieces : List (ℝ × ℝ)

namespace PLFun

/-- Well-formedness (§2, p. 6): at least one piece, the first break point is `b₁ = 0`, the
break points are strictly increasing, and every slope magnitude is positive. -/
def WF (f : PLFun) : Prop :=
  f.pieces ≠ [] ∧ (f.pieces.head?).map Prod.fst = some 0 ∧
    (f.pieces.map Prod.fst).Pairwise (· < ·) ∧ ∀ e ∈ f.pieces, 0 < e.2

/-- Total decrease from the start of the first listed piece up to `x`:
`Σ_k λ_k · (clamp of x to [s_k, s_{k+1}] − s_k)`, the last piece being unbounded above. -/
noncomputable def drop : List (ℝ × ℝ) → ℝ → ℝ
  | [], _ => 0
  | [e], x => e.2 * (max x e.1 - e.1)
  | e :: e' :: rest, x => e.2 * (min (max x e.1) e'.1 - e.1) + drop (e' :: rest) x

/-- Slope magnitude of the first piece. -/
def firstSlope (f : PLFun) : ℝ := (f.pieces.headD (0, 0)).2

/-- The utility at price `x`: for `x ≥ 0` the formula of §2, p. 6,
`v(x) = v(0) − Σ_{j<i} λ_j (b_{j+1} − b_j) − λ_i (x − b_i)` for `x ∈ [b_i, b_{i+1}]`;
for `x < 0` the first piece is extended linearly, `v(x) = v(0) − λ₁ x`. -/
noncomputable def eval (f : PLFun) (x : ℝ) : ℝ :=
  if x < 0 then f.base - f.firstSlope * x else f.base - drop f.pieces x

/-- The left derivative magnitude at `x`: the slope of the last piece starting strictly
below `x`, or the first slope if there is none. -/
noncomputable def leftSlope (f : PLFun) (x : ℝ) : ℝ :=
  (((f.pieces.filter (fun e => decide (e.1 < x))).getLast?).map Prod.snd).getD f.firstSlope

/-- The genuine kinks: the starts `s_k` (`k ≥ 2`) at which the slope actually changes. -/
noncomputable def kinks (f : PLFun) : List ℝ :=
  (f.pieces.zip f.pieces.tail).filterMap
    (fun ee => if ee.1.2 ≠ ee.2.2 then some ee.2.1 else none)

end PLFun

/-- A rent-division instance with `n` agents and `n` rooms: `v a r` is agent `a`'s utility
function for room `r`. -/
structure Instance (n : ℕ) where
  v : Fin n → Fin n → PLFun

variable {n : ℕ}

/-- Standing assumption of §2 ("Throughout"): every utility is a well-formed continuous,
strictly decreasing piecewise-linear function. -/
def Standing (I : Instance n) : Prop := ∀ a r, (I.v a r).WF

/-- `ℓ`, the total number of given linear pieces. -/
def totalPieces (I : Instance n) : ℕ := ∑ a, ∑ r, (I.v a r).pieces.length

/-- Envy-freeness (p. 7): `v_a(π(a), p_{π(a)}) ≥ v_a(r, p_r)` for all `a, r`. -/
def IsEF (I : Instance n) (π : Equiv.Perm (Fin n)) (p : Fin n → ℝ) : Prop :=
  ∀ a r, (I.v a r).eval (p r) ≤ (I.v a (π a)).eval (p (π a))

/-- Definition 2 (p. 8): `ε`-approximate envy-freeness. -/
def IsEpsEF (I : Instance n) (ε : ℝ) (π : Equiv.Perm (Fin n)) (p : Fin n → ℝ) : Prop :=
  ∀ a, (0 ≤ (I.v a (π a)).eval (p (π a)) →
          ∀ r, (I.v a r).eval (p r) ≤ (1 + ε) * (I.v a (π a)).eval (p (π a))) ∧
       ((I.v a (π a)).eval (p (π a)) < 0 →
          ∀ r, (1 + ε) * (I.v a r).eval (p r) ≤ (I.v a (π a)).eval (p (π a)))

/-- Edge `(a, r)` of the first-choice graph `F(p)` (p. 7). -/
def FirstChoice (I : Instance n) (p : Fin n → ℝ) (a r : Fin n) : Prop :=
  ∀ r', (I.v a r').eval (p r') ≤ (I.v a r).eval (p r)

/-- Weight `w(σ) = Σ_a log λ^a_{σ(a)}` of an assignment in `F_w(p)` (p. 7, p. 12), `λ` the
slope of the linear domain containing `p`, i.e. the left derivative at `p`. -/
noncomputable def weight (I : Instance n) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ a, Real.log ((I.v a (σ a)).leftSlope (p (σ a)))

/-- `σ` is a maximum-weight perfect matching of `F_w(p)`. -/
def IsMaxWeightPM (I : Instance n) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ a, FirstChoice I p a (σ a)) ∧
    ∀ τ : Equiv.Perm (Fin n), (∀ a, FirstChoice I p a (τ a)) → weight I p τ ≤ weight I p σ

/-- Boundary points of room `r`'s linear domains: the price `0` together with every kink of
every agent's utility for room `r`. -/
noncomputable def bd (I : Instance n) (r : Fin n) : Finset ℝ :=
  insert 0 (Finset.univ.biUnion fun a => ((I.v a r).kinks).toFinset)

/-- Lower end `L_r` of the linear domain of `p` (Definition 1, p. 7); `⊥` if unbounded. -/
noncomputable def domL (I : Instance n) (p : Fin n → ℝ) (r : Fin n) : WithBot ℝ :=
  ((bd I r).filter (fun b => b < p r)).max

/-- Upper end `U_r` of the linear domain of `p` (Definition 1, p. 7); `⊤` if unbounded. -/
noncomputable def domU (I : Instance n) (p : Fin n → ℝ) (r : Fin n) : WithTop ℝ :=
  ((bd I r).filter (fun b => p r ≤ b)).min

/-- Feasibility for `LP(L, U, π)` of Algorithm 1, line 7. -/
def LPFeasible (I : Instance n) (L : Fin n → WithBot ℝ) (U : Fin n → WithTop ℝ)
    (π : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : Prop :=
  (∀ r, L r ≤ (x r : WithBot ℝ)) ∧ (∀ r, (x r : WithTop ℝ) ≤ U r) ∧ IsEF I π x ∧
    ∀ r, 0 ≤ x r

/-- `x` is an optimal solution of `LP(L, U, π)`: feasible and of minimum total rent. -/
def IsLPOpt (I : Instance n) (L : Fin n → WithBot ℝ) (U : Fin n → WithTop ℝ)
    (π : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : Prop :=
  LPFeasible I L U π x ∧ ∀ y, LPFeasible I L U π y → ∑ r, x r ≤ ∑ r, y r

/-- `v̂` of equation (1), p. 10: the pieces of `f` starting below `M`, followed by a slope-1
piece from `M` on, so `v̂(x) = v(x)` for `x ≤ M` and `v̂(x) = v(M) − (x − M)` for `x > M`. -/
noncomputable def extendQL (M : ℝ) (f : PLFun) : PLFun :=
  ⟨f.base, f.pieces.filter (fun e => decide (e.1 < M)) ++ [(M, 1)]⟩

/-- The modified instance `Î` of Algorithm 1, Steps 1–2. -/
noncomputable def hatInst (M : ℝ) (J : Instance n) : Instance n := ⟨fun a r => extendQL M (J.v a r)⟩

/-- The threshold of p. 10: `v_a(r, M) < v_a(r', 0)` for all agents `a` and rooms `r, r'`. -/
def IsThreshold (J : Instance n) (M : ℝ) : Prop :=
  ∀ a r r', (J.v a r).eval M < (J.v a r').eval 0

/-- A run of Algorithm 1 on `J` with threshold `M` performing `T` while-iterations:
`(π 0, p 0)` is any envy-free solution of `Î` with `p⁰ ≥ M𝟙` (Step 2); for each executed
iteration the guard of line 4 holds, `π (i+1)` is any maximum-weight perfect matching of
`F_w(pⁱ)` (line 6) and `p (i+1)` any optimal solution of `LP(Lⁱ, Uⁱ, π^{i+1})` (line 7). -/
def IsRun (J : Instance n) (M : ℝ) (T : ℕ) (π : ℕ → Equiv.Perm (Fin n))
    (p : ℕ → Fin n → ℝ) : Prop :=
  IsEF (hatInst M J) (π 0) (p 0) ∧ (∀ r, M ≤ p 0 r) ∧
    ∀ i < T, (∀ r, 0 < p i r) ∧ IsMaxWeightPM (hatInst M J) (p i) (π (i + 1)) ∧
      IsLPOpt (hatInst M J) (domL (hatInst M J) (p i)) (domU (hatInst M J) (p i))
        (π (i + 1)) (p (i + 1))

/-- The while-guard fails after `T` iterations: some room's rent is `≤ 0`. -/
def Halted (p : ℕ → Fin n → ℝ) (T : ℕ) : Prop := ∃ r, p T r ≤ 0

/-- Auxiliary for `refineZero`: `h` is the value at the start of the first listed piece;
the zero `s + h/λ` of a piece is inserted when it lies strictly inside that piece. -/
noncomputable def refineAux : ℝ → List (ℝ × ℝ) → List (ℝ × ℝ)
  | _, [] => []
  | h, [e] => if 0 < h then [e, (e.1 + h / e.2, e.2)] else [e]
  | h, e :: e' :: rest =>
      if 0 < h ∧ h - e.2 * (e'.1 - e.1) < 0 then
        e :: (e.1 + h / e.2, e.2) :: refineAux (h - e.2 * (e'.1 - e.1)) (e' :: rest)
      else e :: refineAux (h - e.2 * (e'.1 - e.1)) (e' :: rest)

/-- The zero `z^a_r` of `f` treated as a break point (p. 16). -/
noncomputable def refineZero (f : PLFun) : PLFun := ⟨f.base, refineAux f.base f.pieces⟩

/-- `λ̄ = (1+ε)^⌈log_{1+ε} λ⌉` (p. 16). -/
noncomputable def roundUp (ε l : ℝ) : ℝ := (1 + ε) ^ (⌈Real.logb (1 + ε) l⌉ : ℤ)

/-- The split point `x*` of the piece `[x₁, x₂]` with slope `λ` (p. 16): the solution of
`H = B + λ̄ (x₂ − x*) + (λ̄/(1+ε)) (x* − x₁)` with `H − B = λ (x₂ − x₁)`. -/
noncomputable def xStar (ε x₁ x₂ l : ℝ) : ℝ :=
  x₁ + (1 + ε) * (roundUp ε l - l) * (x₂ - x₁) / (ε * roundUp ε l)

/-- Rounding of the pieces (p. 16): a bounded piece `[x₁, x₂]` becomes a piece of slope
`λ̄/(1+ε)` on `[x₁, x*)` and one of slope `λ̄` on `[x*, x₂]` (only the latter if `x* = x₁`);
the unbounded last piece gets slope `λ̄/(1+ε)`. -/
noncomputable def roundAux (ε : ℝ) : List (ℝ × ℝ) → List (ℝ × ℝ)
  | [] => []
  | [e] => [(e.1, roundUp ε e.2 / (1 + ε))]
  | e :: e' :: rest =>
      (if xStar ε e.1 e'.1 e.2 = e.1 then [(e.1, roundUp ε e.2)]
        else [(e.1, roundUp ε e.2 / (1 + ε)), (xStar ε e.1 e'.1 e.2, roundUp ε e.2)]) ++
        roundAux ε (e' :: rest)

/-- `v̄` for a single utility function (p. 16): base value unchanged, pieces rounded. -/
noncomputable def roundPL (ε : ℝ) (f : PLFun) : PLFun := ⟨f.base, roundAux ε f.pieces⟩

/-- The slope-rounded instance `Ī` of §5 (zero split first, then rounding). -/
noncomputable def roundInst (ε : ℝ) (I : Instance n) : Instance n :=
  ⟨fun a r => roundPL ε (refineZero (I.v a r))⟩

/-- Powers-of-`(1+ε)` property (§4, p. 10): every slope is `(1+ε)^k` for an integer `k`. -/
def PowersProp (ε : ℝ) (J : Instance n) : Prop :=
  ∀ a r, ∀ e ∈ (J.v a r).pieces, ∃ k : ℤ, e.2 = (1 + ε) ^ k

end FairRentFPTAS.Approx


