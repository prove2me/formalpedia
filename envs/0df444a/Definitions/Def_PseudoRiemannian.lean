-- Prove2me | Definitions.Def_PseudoRiemannian
-- name    : PseudoRiemannian
-- status  : Definition
-- author  : @LG
-- created : 2026-11-27T02:28:40.570236+00:00
-- url     : https://prove2.me/theorems/2b8f4b77-e140-5203-b308-573c33e24a38
-- title:
--   Pseudo-Riemannian metrics: smooth symmetric nondegenerate tensors of constant signature
-- statement:
--   This definition file introduces, in the namespace `PseudoRiemannian`, the notions used to formalize pseudo-Riemannian metrics — the metric tensors of the source, "non-degenerate, smooth, symmetric, bilinear", of constant signature — on plain coordinate spaces of arbitrary dimension $n$ (the tangent spaces, "pseudo-Euclidean vector spaces" in the source's sense), with no manifold machinery.
--
--   **1. Spaces.** `Spc n = Fin n → ℝ` — plain real `n`-tuples; a metric is a field of matrices `g : Spc n → Matrix (Fin n) (Fin n) ℝ`.
--
--   **2. Signature vectors (`IsSignVec`).** `s : Fin n → ℝ` with `s i = -1 ∨ s i = 1` for every `i` — the diagonal of a normal form under an orthogonal change of basis.
--
--   **3. Smoothness (`IsSmooth`).** Every component of the metric is $C^\infty$: `∀ i j, ContDiff ℝ ∞ (fun x => g x i j)`.
--
--   **4. Symmetry (`IsSymmetric`).** $g(x)_{ij} = g(x)_{ji}$ at every point — the source's $g(X,Y) = g(Y,X)$.
--
--   **5. Signature witness (`HasSignature g s`).** At every point there is an invertible matrix $B$ with
--
--   $$B^{T}\, g(x)\, B \;=\; \mathrm{diag}(s).$$
--
--   One piece of carried data encoding both defining requirements of the source: nondegeneracy everywhere, and constancy of the signature along the manifold ("the non-degeneracy condition together with continuity implies that p and q remain unchanged throughout the manifold").
--
--   **6. Pseudo-Riemannian metric (`IsPseudoRiemannian g s`).** `IsSymmetric g ∧ IsSmooth g ∧ HasSignature g s` — the source's "differentiable manifold with a metric tensor that is everywhere nondegenerate", with the signature carried explicitly.
--
--   **7. The pairing (`pair g x u v`).** The value $g_x(u, v)$ in components:
--
--   $$\mathrm{pair}(g, x, u, v) \;=\; \sum_{i}\sum_{j}\ u_i\, g(x)_{ij}\, v_j,$$
--
--   bilinear in $u, v$; symmetric in $u, v$ at points where $g$ is symmetric.
--
--   **8. Nondegeneracy (`IsNondegenerateAt g x`).** The article's condition verbatim: "there is no non-zero X such that g(X, Y) = 0 for all Y" — the only `u` with `pair g x u v = 0` for **all** `v` is `u = 0`.
--
--   **9. The index (`negCount s`).** The number of negative entries of the signature diagonal — the `q` of the signature `(p, q)`; well defined only up to the goal theorem (Sylvester's law of inertia).
--
--   **10. The model space (`minkDiag`, `etaM`).** The signature diagonal `(-1, 1, 1, 1)` and the flat Minkowski metric matrix — the constant metric of the model space $R^{1,3}$, "the local model of a Lorentzian manifold".
--
--   **Formalization note.** No manifold machinery: a single global coordinate space `Fin n → ℝ`, Mathlib `Matrix` algebra, and `ContDiff ℝ ∞` for smoothness (Mathlib's `∞` smoothness order, `open scoped ContDiff`). The causal classification timelike/null/spacelike is out of scope here (formalized in the platform's Special Relativity and World Lines missions); so are Levi-Civita connections, curvature, geodesics and completeness — see the mission description.
-- source:
--   Wikipedia, Pseudo-Riemannian manifold, https://en.wikipedia.org/wiki/Pseudo-Riemannian_manifold (source of the quoted statements, reproduced verbatim in the definition file)

import Mathlib

/-!
Pseudo-Riemannian manifolds — smooth symmetric nondegenerate metric tensors of
constant signature, formalized in a concrete framework on plain coordinate
spaces of arbitrary dimension.

Source: Wikipedia, *Pseudo-Riemannian manifold*,
https://en.wikipedia.org/wiki/Pseudo-Riemannian_manifold .  Exact source
statements:

"In mathematical physics, a pseudo-Riemannian manifold, also called a
semi-Riemannian manifold, is a differentiable manifold with a metric tensor
that is everywhere nondegenerate.  This is a generalization of a Riemannian
manifold in which the requirement of positive-definiteness is relaxed."
"Every tangent space of a pseudo-Riemannian manifold is a pseudo-Euclidean
vector space."  "A special case used in general relativity is a
four-dimensional Lorentzian manifold for modeling spacetime, where tangent
vectors can be classified as timelike, null, and spacelike."

On the metric tensor: "A metric tensor is a non-degenerate, smooth, symmetric,
bilinear map that assigns a real number to pairs of tangent vectors at each
tangent space of the manifold"; symmetry and bilinearity read `g(X, Y) = g(Y,
X)` and `g(aX + Y, Z) = a g(X, Z) + g(Y, Z)`; "That g is non-degenerate means
there is no non-zero X in TpM such that g(X, Y) = 0 for all Y in TpM."

On signature: "By Sylvester's law of inertia, the number of each positive,
negative and zero values produced in this manner are invariants of the metric
tensor, independent of the choice of orthogonal basis. The signature (p, q, r)
of the metric tensor gives these numbers ... A non-degenerate metric tensor has
r = 0 and the signature may be denoted (p, q), where p + q = n."  "The
non-degeneracy condition together with continuity implies that p and q remain
unchanged throughout the manifold (assuming it is connected)."

Lorentzian manifolds: signature `(1, n-1)` (equivalently `(n-1, 1)`); "A
principal premise of general relativity is that spacetime can be modeled as a
4-dimensional Lorentzian manifold of signature (3, 1) or, equivalently, (1, 3).
Unlike Riemannian manifolds with positive-definite metrics, an indefinite
signature allows tangent vectors to be classified into timelike, null or
spacelike."

Model space: "the model space for a pseudo-Riemannian manifold of signature
(p, q) is pseudo-Euclidean space R^{p,q}, for which there exist coordinates x_i
such that g = dx1^2 + ... + dxp^2 - dx_{p+1}^2 - ... - dx_{p+q}^2"; "Minkowski
space R^{n-1,1} with the flat Minkowski metric is the local model of a
Lorentzian manifold."

Scope, disclosed.  No manifold machinery: the mission works on the plain
coordinate space `Spc n = Fin n -> R` (the tangent spaces, pseudo-Euclidean
vector spaces in the source's sense) with the metric as a smooth field of
symmetric matrices.  Smoothness is `ContDiff R infinity` of every component.
The constant signature is carried as a signature witness: at every point an
invertible congruence `B^T (g x) B = diag s` to a fixed diagonal of `+- 1`
entries — this encodes nondegeneracy and the invariance of the signature along
the manifold in one piece of data.  The theorems: invertibility of the metric
matrix from a witness; the article's nondegeneracy condition; the Minkowski
model `R^{1,3}` (the Lorentzian case of general relativity); the Riemannian
special case (all-plus signature gives positive definiteness — the requirement
relaxed by the source's definition, here shown to be exactly recovered); and
the goal, Sylvester's law of inertia in the diagonal form the article invokes —
the number of negative entries of the signature diagonal is the same for every
witness, so the signature `(p, q)` of the metric is well defined.

What is NOT formalized: manifolds and coordinate patches (the framework is a
single global coordinate space), the Levi-Civita connection and curvature (the
fundamental theorem of (pseudo-)Riemannian geometry), geodesics and
completeness (Hopf-Rinow, the Clifton-Pohl torus), topological obstructions to
metrics of given signature, submanifold inheritance, and the causal
classification timelike/null/spacelike (formalized in the platform's separate
Special Relativity and World Lines missions).
-/

namespace PseudoRiemannian

open Matrix
open scoped ContDiff

variable {n : ℕ}

/-- Tangent/cotangent space: plain real `n`-tuples — a pseudo-Euclidean vector
space when equipped with the pairing below. -/
abbrev Spc (n : ℕ) := Fin n → ℝ

/-- A signature vector: entries `± 1` only — the diagonal of an orthogonal
basis normal form. -/
def IsSignVec (s : Fin n → ℝ) : Prop := ∀ i, s i = -1 ∨ s i = 1

/-- Symmetry of the metric: `g(x, Y) = g(Y, x)` in components. -/
def IsSymmetric (g : Spc n → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x i j, g x i j = g x j i

/-- Smoothness of the metric: every component is `C^∞`. -/
def IsSmooth (g : Spc n → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)

/-- Constant-signature witness: at every point, an invertible congruence to the
fixed signature diagonal `diag s` — nondegeneracy and constancy of the
signature along the manifold, in one piece of carried data. -/
def HasSignature (g : Spc n → Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ) : Prop :=
  ∀ x, ∃ B : Matrix (Fin n) (Fin n) ℝ, IsUnit B.det ∧ Bᵀ * g x * B = Matrix.diagonal s

/-- A pseudo-Riemannian metric of signature vector `s`: smooth, symmetric,
with constant signature witness. -/
def IsPseudoRiemannian (g : Spc n → Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ) : Prop :=
  IsSymmetric g ∧ IsSmooth g ∧ HasSignature g s

/-- The metric pairing `g_x(u, v)` in components — bilinear in `u, v` by the
double sum, symmetric at `x` when `g` is symmetric. -/
def pair (g : Spc n → Matrix (Fin n) (Fin n) ℝ) (x : Spc n) (u v : Spc n) : ℝ :=
  ∑ i, ∑ j, u i * g x i j * v j

/-- The article's nondegeneracy: "there is no non-zero X such that g(X, Y) = 0
for all Y". -/
def IsNondegenerateAt (g : Spc n → Matrix (Fin n) (Fin n) ℝ) (x : Spc n) : Prop :=
  ∀ u : Spc n, (∀ v : Spc n, pair g x u v = 0) → u = 0

/-- The index `q` of a signature: the number of negative entries of the
signature diagonal. -/
noncomputable def negCount (s : Fin n → ℝ) : ℕ := (Finset.univ.filter fun i => s i < 0).card

/-- The signature diagonal `(-1, 1, 1, 1)` — Lorentzian signature `(1, 3)`
(with the opposite sign convention) of general-relativistic spacetime. -/
def minkDiag : Fin 4 → ℝ := fun i => if i = 0 then -1 else 1

/-- The flat Minkowski metric matrix — the constant metric of the model space
`R^{1,3}`. -/
def etaM : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal minkDiag

end PseudoRiemannian


