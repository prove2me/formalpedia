-- Prove2me | Definitions.Def_UncoupledDyn_Continuum_Setting
-- name    : UncoupledDyn_Continuum_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:16.489407+00:00
-- url     : https://prove2.me/theorems/d671eb81-0cea-4496-85bc-fa086ee488f4
-- title:
--   §I, §II and Appendix, pp. 1830–1835 — two-player unit-disk games, pure Nash equilibrium, uncoupled (2), Nash-convergent, fn. 7 neighborhood, 𝒰₀, φ, Γ₀, ψ_a
-- statement:
--   This file fixes the objects of Hart and Mas-Colell (2003), §I (*The Model*), §II (*An Example with a Continuum of Strategies*) and the Appendix.
--
--   **Strategies and profiles.** There are two players. Each player's strategy set is the closed unit disk
--   $$D=\{z\in\mathbb R^2:\ \|z\|\le 1\},$$
--   and a strategy profile is a pair $x=(x^1,x^2)\in X:=D\times D$. The set $X$ is the domain of the dynamics.
--
--   **Games.** A game $\Gamma=(u^1,u^2)$ is a pair of payoff functions $u^i:X\to\mathbb R$. A profile $\bar x\in X$ is a (pure) **Nash equilibrium** of $\Gamma$ if no player gains by a unilateral deviation: $u^i(z,\bar x^{j})\le u^i(\bar x^i,\bar x^j)$ for each $i$ and every $z\in D$. A game $\Gamma$ lies in the **$\varepsilon$-neighborhood** of $\Gamma_0=(u_0^1,u_0^2)$ (fn. 7) if $|u^i(s)-u_0^i(s)|<\varepsilon$ for every profile $s\in X$ and both players $i$.
--
--   **Dynamics.** A dynamic for a family $\mathcal U$ of games assigns to every game $\Gamma$ a vector field $x\mapsto F(x;\Gamma)$ on $X$, and is read $\dot x=F(x;\Gamma)$, i.e. $\dot x^i=F^i(x;\Gamma)$. It is **uncoupled** ((2), p. 1831) if $F^i$ depends on the game only through $u^i$: whenever two games of $\mathcal U$ give player $i$ the same payoff function on $X$, the $i$-th components of $F$ coincide at every $x\in X$. A **solution** of $\dot x=F(x;\Gamma)$ is a curve $x(t)$, $t\ge 0$, with values in $X$ whose (right) derivative at every $t\ge0$ equals $F(x(t);\Gamma)$.
--
--   **Jacobians.** For a map $f=(f^1,f^2):X\to\mathbb R^2\times\mathbb R^2$ and $x\in X$, the $4\times4$ Jacobian matrix has entry $\partial f^i_k(x)/\partial x^j_l$ in row $(i,k)$ and column $(j,l)$ (players $i,j$, coordinates $k,l$). Its $2\times2$ block $J^i=(\partial f^i_k(x)/\partial x^i_l)_{k,l}$ is player $i$'s own-strategy block. The matrix
--   $$\begin{bmatrix}J^1&-2J^1\\-2J^2&J^2\end{bmatrix}$$
--   of p. 1832 is written in the same (player, coordinate) indexing.
--
--   **Nash-convergence** (p. 1831). A dynamic $F$ is **Nash-convergent** for $\mathcal U$ if for every $\Gamma\in\mathcal U$ and every Nash equilibrium $\bar x$ of $\Gamma$:
--   1. $F(\bar x;\Gamma)=0$;
--   2. $F(\cdot\,;\Gamma)$ is $C^1$ on $X$;
--   3. all eigenvalues of the Jacobian matrix $J$ of $F(\cdot\,;\Gamma)$ at $\bar x$ have negative real parts;
--   4. every solution $x(t)$ converges to $\bar x$ as $t\to\infty$.
--
--   **The family $\mathcal U_0$** (p. 1831). It consists of the games with
--   $$u^i(x^i,x^j)=-\|x^i-\xi^i(x^j)\|^2\qquad(j=3-i),$$
--   where each $\xi^i:D\to D$ is continuous and the equation $\xi^i(\xi^j(x^i))=x^i$ has exactly one solution $x^i\in D$.
--
--   **The map $\varphi$ and the game $\Gamma_0$** (p. 1831). $\varphi(z)=2z$ for $\|z\|\le\frac13$; on the circle $\|z\|=1$, $\varphi$ is the rotation by $\pi/4$; and on each ray, $\varphi$ is affine in the radius $r=\|z\|$ between $r=\frac13$ and $r=1$:
--   $$\varphi(z)=\frac{1-r}{r}\,z+\frac{3r-1}{2r}\,e^{i\pi/4}z\qquad(\tfrac13<r\le1).$$
--   The game $\Gamma_0$ has $u_0^i(x^i,x^j)=-\|x^i-\varphi(x^j)\|^2$.
--
--   **The functions $\psi_a$** (Appendix, p. 1835). For $\varepsilon>0$ and $a$ with $\|a\|<\varepsilon$, writing $r=\|z\|$ and $R_\varepsilon$ for the rotation by the angle $\varepsilon$:
--   $$\psi_a(z)=\begin{cases}a,& r\le2\varepsilon,\\ \frac{3\varepsilon-r}{\varepsilon}\,a,& 2\varepsilon<r\le3\varepsilon,\\ \frac{r-3\varepsilon}{\varepsilon}\,R_\varepsilon\,\varphi\!\left(\frac{4\varepsilon}{r}z\right),& 3\varepsilon<r<4\varepsilon,\\ R_\varepsilon\,\varphi(z),& r\ge4\varepsilon.\end{cases}$$
--   This is (i)–(iv) of the Appendix: $a$ on $r\le2\varepsilon$, $0$ on $r=3\varepsilon$, the rotation of $\varphi(z)$ by $\varepsilon$ on $r\ge4\varepsilon$, and linear interpolation on rays in between.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note.** $\mathbb R^2$ is modelled as $\mathbb C$: $z_1=\operatorname{Re}z$, $z_2=\operatorname{Im}z$, $\|z\|$ is the Euclidean norm, and rotation by $\theta$ is multiplication by $e^{i\theta}$ (counter-clockwise). Players are 0-based: the page's player $i$ is index $i-1$, and the page's $j=3-i$ is `i + 1` in `Fin 2`. A game is a total function on $(\mathbb C)^2$, but only its values on $X$ enter any definition: Nash equilibria, neighborhoods, uncoupledness and $\mathcal U_0$ compare payoffs on $X$ only. Derivatives are taken **within $X$** (`fderivWithin`); $X$ is convex with nonempty interior, so this derivative is unique, and at interior points it is the ordinary derivative. Solutions are required to stay in $X$, so that no statement depends on values of $F$ outside $X$. The Hurwitz condition is the published `FatkhullinPolyak.Discrete.IsHurwitz`, applied to the $4\times4$ Jacobian after reindexing $\{0,1\}\times\{0,1\}\cong\{0,1,2,3\}$ in player-major order $(x^1_1,x^1_2,x^2_1,x^2_2)$ (`finProdFinEquiv`). The C¹ and Jacobian restrictions, which the page imposes on every dynamic it considers, are part of the predicate `NashConvergent`; the page's single-Nash-equilibrium property is not, and appears as a hypothesis of the statements that need it. Nash equilibrium means pure equilibrium; fn. 9 notes that the games of §II have no mixed equilibria. $\varphi$ fixes the page's example angle $\pi/4$, and its values outside $D$ are never used.
-- source:
--   Hart and Mas-Colell, Uncoupled Dynamics Do Not Lead to Nash Equilibrium, Amer. Econ. Rev. 93(5) (2003), pp. 1830–1831, §I (1)–(2), fn. 5, fn. 7; p. 1831, §II (D, φ, Γ₀, 𝒰₀), fn. 8–9; p. 1832, Lemma 2 (Jⁱ), fn. 11, display of J; p. 1835, Appendix (i)–(iv)

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix

namespace UncoupledDyn.Continuum

/-!
Hart and Mas-Colell (2003), *Uncoupled Dynamics Do Not Lead to Nash Equilibrium*, §I (pp. 1830–1831),
§II (pp. 1831–1832) and the Appendix (p. 1835).

Conventions:
* the plane `ℝ²` is modelled as `ℂ` (`z₁ = z.re`, `z₂ = z.im`, `‖z‖` the Euclidean norm; rotation by
  the angle `θ` counter-clockwise is multiplication by `exp (θ i)`);
* players are `Fin 2`, 0-based: the page's player `i` is index `i - 1`, and the page's "other player"
  `j = 3 - i` is `i + 1` in `Fin 2`;
* a state is `x : Fin 2 → ℂ` (`x 0` = the page's `x¹`, `x 1` = the page's `x²`); the domain of the
  dynamics is `X = D × D = Π Sⁱ`;
* a game is the pair of payoff functions `G i : (Fin 2 → ℂ) → ℝ`; only its values on `X` are part of
  the game;
* a dynamic is `F : (Fin 2 → ℂ) → Game → (Fin 2 → ℂ)`, read `ẋ = F(x; Γ)`; only its values at
  `x ∈ X` matter.
-/

/-- The unit disk `D = {z ∈ ℝ² : ‖z‖ ≤ 1}`, each player's strategy set. -/
def D : Set ℂ := Metric.closedBall 0 1

/-- The domain of the dynamics, `X = S¹ × S² = D × D`. -/
def X : Set (Fin 2 → ℂ) := Set.univ.pi (fun _ => D)

/-- A game `Γ = (u¹, u²)`: `G i x` is player `i`'s payoff at the strategy profile `x`. -/
abbrev Game : Type := Fin 2 → (Fin 2 → ℂ) → ℝ

/-- `x` is a (pure) Nash equilibrium of `G`: `x ∈ X` and no player gains by a unilateral deviation
within `D`. -/
def IsNash (G : Game) (x : Fin 2 → ℂ) : Prop :=
  x ∈ X ∧ ∀ i : Fin 2, ∀ z ∈ D, G i (Function.update x i z) ≤ G i x

/-- Footnote 7: `G` lies in the `ε`-neighborhood of `G0`, i.e. `|uⁱ(s) − u₀ⁱ(s)| < ε` for every
profile `s ∈ X` and every player `i`. -/
def IsNear (G G0 : Game) (ε : ℝ) : Prop :=
  ∀ i : Fin 2, ∀ x ∈ X, |G i x - G0 i x| < ε

/-- Uncoupled dynamic (2): for games in `U`, `Fⁱ` depends on the game only through `uⁱ`. If two games
of `U` give player `i` the same payoff function (on `X`), then at every `x ∈ X` the `i`-th component
of `F` is the same. -/
def Uncoupled (U : Set Game) (F : (Fin 2 → ℂ) → Game → (Fin 2 → ℂ)) : Prop :=
  ∀ G ∈ U, ∀ G' ∈ U, ∀ i : Fin 2, (∀ s ∈ X, G i s = G' i s) → ∀ x ∈ X, F x G i = F x G' i

/-- `x : ℝ → (Fin 2 → ℂ)` is a solution of `ẋ = F(x; G)` for `t ≥ 0`: it stays in `X` and its
(right) derivative at every `t ≥ 0` is `F (x t) G`. -/
def IsSolution (F : (Fin 2 → ℂ) → Game → (Fin 2 → ℂ)) (G : Game) (x : ℝ → (Fin 2 → ℂ)) : Prop :=
  ∀ t : ℝ, 0 ≤ t → x t ∈ X ∧ HasDerivWithinAt x (F (x t) G) (Set.Ici 0) t

/-- The standard basis of `ℂ ≅ ℝ²`: `e₁ = 1`, `e₂ = i`. -/
def basisVec : Fin 2 → ℂ := ![1, Complex.I]

/-- The coordinates of `z ∈ ℂ ≅ ℝ²`: `z₁ = re z`, `z₂ = im z`. -/
def coord : Fin 2 → ℂ → ℝ := ![Complex.re, Complex.im]

/-- The `4 × 4` real Jacobian matrix of `f : X → ℝ⁴` at `x`, the derivative being taken within `X`:
the entry at row `(i, k)` and column `(j, l)` is `∂fⁱ_k(x)/∂xʲ_l`. Rows and columns are indexed by
(player, coordinate). -/
noncomputable def jacOf (f : (Fin 2 → ℂ) → (Fin 2 → ℂ)) (x : Fin 2 → ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  fun p q => coord p.2 ((fderivWithin ℝ f X x) (Pi.single q.1 (basisVec q.2)) p.1)

/-- The `2 × 2` own-strategy block `(∂fⁱ_k(x)/∂xⁱ_l)_{k,l}` of `jacOf f x`. -/
noncomputable def ownJacOf (f : (Fin 2 → ℂ) → (Fin 2 → ℂ)) (i : Fin 2) (x : Fin 2 → ℂ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun k l => jacOf f x (i, k) (i, l)

/-- The Jacobian matrix `J` of `F( · ; G)` at `x`. -/
noncomputable def jac (F : (Fin 2 → ℂ) → Game → (Fin 2 → ℂ)) (G : Game) (x : Fin 2 → ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  jacOf (fun y => F y G) x

/-- Lemma 2's matrix `Jⁱ = (∂Fⁱ_k(x; uⁱ)/∂xⁱ_l)_{k,l=1,2}` for the game `G`. -/
noncomputable def ownJac (F : (Fin 2 → ℂ) → Game → (Fin 2 → ℂ)) (G : Game) (i : Fin 2)
    (x : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ownJacOf (fun y => F y G) i x

/-- The `4 × 4` block matrix `[J¹, −2J¹; −2J², J²]` of p. 1832, with rows and columns indexed by
(player, coordinate) in the same order as `jacOf`: the entry at row `(i, k)` and column `(j, l)` is
`Jⁱ_{kl}` if `j = i` and `−2 Jⁱ_{kl}` if `j ≠ i`. -/
def blockJ (J1 J2 : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  fun p q => if q.1 = p.1 then ![J1, J2] p.1 p.2 q.2 else -2 * ![J1, J2] p.1 p.2 q.2

/-- Nash-convergent dynamic for `U` (p. 1831), together with the regularity the page always imposes:
for every game `G ∈ U` and every Nash equilibrium `xbar` of `G`,
`F(xbar; G) = 0`, `F( · ; G)` is `C¹` on `X`, the Jacobian of `F( · ; G)` at `xbar` has only
eigenvalues with negative real part, and every solution converges to `xbar`. -/
def NashConvergent (U : Set Game) (F : (Fin 2 → ℂ) → Game → (Fin 2 → ℂ)) : Prop :=
  ∀ G ∈ U, ∀ xbar : Fin 2 → ℂ, IsNash G xbar →
    F xbar G = 0 ∧ ContDiffOn ℝ 1 (fun y => F y G) X ∧
    FatkhullinPolyak.Discrete.IsHurwitz
      (Matrix.reindex finProdFinEquiv finProdFinEquiv (jac F G xbar)) ∧
    ∀ x : ℝ → (Fin 2 → ℂ), IsSolution F G x → Filter.Tendsto x Filter.atTop (nhds xbar)

/-- The family `𝒰₀` of §II: games with `uⁱ(xⁱ, xʲ) = −‖xⁱ − ξⁱ(xʲ)‖²` on `X`, where each
`ξⁱ : D → D` is continuous and the equation `ξⁱ(ξʲ(xⁱ)) = xⁱ` has a unique solution in `D`. -/
def U0 : Set Game :=
  {G | ∃ ξ : Fin 2 → ℂ → ℂ, (∀ i, ContinuousOn (ξ i) D ∧ Set.MapsTo (ξ i) D D) ∧
    (∀ i, ∃! z, z ∈ D ∧ ξ i (ξ (i + 1) z) = z) ∧
    ∀ i, ∀ x ∈ X, G i x = -‖x i - ξ i (x (i + 1))‖ ^ 2}

/-- The explicit `φ` of p. 1831: `φ(z) = 2z` for `‖z‖ ≤ 1/3`; on `‖z‖ = 1` a rotation by `π/4`;
affine in the radius on each ray between `‖z‖ = 1/3` and `‖z‖ = 1`. Writing `r = ‖z‖`, for
`1/3 < r` this is `((1 − r)/r) z + ((3r − 1)/(2r)) e^{iπ/4} z`. -/
noncomputable def phi (z : ℂ) : ℂ :=
  if ‖z‖ ≤ 1 / 3 then 2 * z
  else (((1 - ‖z‖) / ‖z‖ : ℝ) : ℂ) * z +
    (((3 * ‖z‖ - 1) / (2 * ‖z‖) : ℝ) : ℂ) * (Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) * z)

/-- The game `Γ₀` of §II: `u₀ⁱ(xⁱ, xʲ) = −‖xⁱ − φ(xʲ)‖²`. -/
noncomputable def Gamma0 : Game := fun i x => -‖x i - phi (x (i + 1))‖ ^ 2

/-- Rotation of `w ∈ ℂ ≅ ℝ²` by the angle `θ` (counter-clockwise). -/
noncomputable def rot (θ : ℝ) (w : ℂ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I) * w

/-- The Appendix's `ψ_a` (p. 1835), for `ε > 0` and `a ∈ D` with `‖a‖ < ε`, writing `r = ‖z‖`:
(i) `ψ_a(z) = a` for `r ≤ 2ε`; (ii) `ψ_a(z) = 0` for `r = 3ε`; (iii) `ψ_a(z)` is the rotation of
`φ(z)` by the angle `ε` for `r ≥ 4ε`; (iv) affine in `r` on each ray in `2ε < r < 3ε` and in
`3ε < r < 4ε`. -/
noncomputable def psi (ε : ℝ) (a z : ℂ) : ℂ :=
  if ‖z‖ ≤ 2 * ε then a
  else if ‖z‖ ≤ 3 * ε then (((3 * ε - ‖z‖) / ε : ℝ) : ℂ) * a
  else if ‖z‖ < 4 * ε then
    (((‖z‖ - 3 * ε) / ε : ℝ) : ℂ) * rot ε (phi ((((4 * ε) / ‖z‖ : ℝ) : ℂ) * z))
  else rot ε (phi z)

end UncoupledDyn.Continuum


