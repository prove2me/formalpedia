-- Prove2me | Definitions.Def_OptQJunta_nuJ
-- name    : OptQJunta_nuJ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:31.169147+00:00
-- url     : https://prove2.me/theorems/afd8dc43-d0dd-41c1-b94f-81240816e053
-- title:
--   Pair-fiber disagreement $\nu_J$ and minority densities $\mu_u$
-- statement:
--   Fix $f:\{0,1\}^n\to\{0,1\}$ and $J\subseteq[n]$, and let $X,Y$ be independent and uniform on $\{0,1\}^n$. The **pair-fiber disagreement** is
--
--   $$
--   \nu_J=\Pr\bigl[f(X)\neq f(Y)\mid X_J=Y_J\bigr].
--   $$
--
--   For $u\in\{0,1\}^{|J|}$, the **fiber** of $u$ is $\{x:x_J=u\}$, and the **minority density** $\mu_u$ is the fraction of the fiber on which $f$ takes its less frequent value.
--
--   These quantities measure how far $f$ is from being determined by the coordinates in $J$; the partial support recovery procedure of §4.1.1 stops when $\nu_J$ is small.
--
--   **Formalization Note** $\nu_J$ is the ratio of the number of pairs $(x,y)$ with $x_J=y_J$ and $f(x)\ne f(y)$ to the number of pairs with $x_J=y_J$; the latter is positive. $u$ is a function `J → Bool`, and $\mu_u=\min(\#\{f=0\},\#\{f=1\})/\#\text{fiber}$ with a fiber of $2^{n-|J|}\ge1$ points.
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), §4.1.1, p.55

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace OptQJunta

open QAlgorithms

/-- The pair-fiber disagreement `ν_J = Pr[f(X) ≠ f(Y) | X_J = Y_J]` for `X, Y` independent uniform on
`{0,1}^n` (Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026,
sha256 a97d09a4…, §4.1.1, p.55).

**Formalization Note** The conditional probability is the ratio of pair counts; the conditioning
event has positive probability (it contains every pair `(x, x)`), so the ratio is never `0/0`. -/
noncomputable def nuJ {n : ℕ} (f : Qubits n → Bool) (J : Finset (Fin n)) : ℝ :=
  ((Finset.univ.filter fun p : Qubits n × Qubits n =>
      (∀ i ∈ J, p.1 i = p.2 i) ∧ f p.1 ≠ f p.2).card : ℝ) /
    ((Finset.univ.filter fun p : Qubits n × Qubits n => ∀ i ∈ J, p.1 i = p.2 i).card : ℝ)

/-- The fiber `{x : x_J = u}` of `u ∈ {0,1}^{|J|}` (Bao–Gao–Yao preprint, version of November 3, 2026,
sha256 a97d09a4…, §4.1.1, p.55).

**Formalization Note** `u ∈ {0,1}^{|J|}` is a function `J → Bool` on the coordinates of `J`
(the paper orders them by index; this changes no instance). -/
def fiber {n : ℕ} (J : Finset (Fin n)) (u : J → Bool) : Finset (Qubits n) :=
  Finset.univ.filter fun x => ∀ i : J, x i = u i

/-- The minority density `μ_u` of `f` on the fiber `{x : x_J = u}` (Bao–Gao–Yao preprint, version of
November 3, 2026, sha256 a97d09a4…, §4.1.1, p.55): the fraction of the fiber on which `f` takes its
less frequent value, `min(#{f = 0}, #{f = 1}) / #fiber`. The fiber has `2^{n−|J|} ≥ 1` points. -/
noncomputable def minorityDensity {n : ℕ} (f : Qubits n → Bool) (J : Finset (Fin n))
    (u : J → Bool) : ℝ :=
  (min ((fiber J u).filter fun x => f x = false).card
      ((fiber J u).filter fun x => f x = true).card : ℝ) / ((fiber J u).card : ℝ)

end OptQJunta


