-- Prove2me | Definitions.Def_OptQJunta_IsFar
-- name    : OptQJunta_IsFar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:40.21991+00:00
-- url     : https://prove2.me/theorems/82ae1233-b6d9-4c8d-94ed-581a2abd48e4
-- title:
--   $T$-juntas, $k$-juntas $\mathcal B_k$, uniform Hamming distance, $\mathrm{dist}_{\mathcal B}(f,\mathcal B_T)$ and $\varepsilon$-far
-- statement:
--   For $T\subseteq[n]$, a Boolean function $f:\{0,1\}^n\to\{0,1\}$ is a **$T$-junta**, $f\in\mathcal B_T^{(n)}$, if $f(x)=f_T(x_T)$ for some $f_T:\{0,1\}^{|T|}\to\{0,1\}$; it is a **$k$-junta**, $f\in\mathcal B_k^{(n)}=\bigcup_{|T|\le k}\mathcal B_T^{(n)}$, if it is a $T$-junta for some $T$ with $|T|\le k$ (Definition 2.13). The **uniform Hamming distance** (Definition 2.14) is
--
--   $$
--   \mathrm{dist}_{\mathcal B}(f,g)=\Pr_{x\sim\mathrm{Unif}(\{0,1\}^n)}[f(x)\neq g(x)],
--   $$
--
--   and for a nonempty class $\mathcal S$, $\mathrm{dist}_{\mathcal B}(f,\mathcal S)=\min_{g\in\mathcal S}\mathrm{dist}_{\mathcal B}(f,g)$; the module defines $\mathrm{dist}_{\mathcal B}(f,\mathcal B_T)$. A function is **$\varepsilon$-far** from $\mathcal B_k$ if $\mathrm{dist}_{\mathcal B}(f,\mathcal B_k)\ge\varepsilon$.
--
--   These are the YES and NO classes of junta testing (Problem 4.1).
--
--   **Formalization Note** "$f$ is a function of $x_T$" is stated as: inputs that agree on $T$ have the same value. $\mathrm{dist}_{\mathcal B}(f,\mathcal B_T)$ is a minimum over the finite set of $T$-juntas, which contains the constants. "$\varepsilon$-far" is stated as $\varepsilon\le\mathrm{dist}_{\mathcal B}(f,g)$ for every $k$-junta $g$, which is equivalent because $\mathcal B_k$ is finite and nonempty.
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Definitions 2.13–2.14, pp.16–17

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace OptQJunta

open QAlgorithms

/-- **Definition 2.13** (Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3,
2026, sha256 a97d09a4…, p.16): `f ∈ ℬ^{(n)}_T`, i.e. `f(x) = f_T(x_T)` for some `f_T`: the value of `f`
depends only on the coordinates in `T`.

**Formalization Note** Bits are `Bool`, `{0,1}^n` is `QAlgorithms.Qubits n`, coordinates `Fin n`
(0-based). "`f` is a function of `x_T`" is stated as: inputs agreeing on `T` have the same value. -/
def IsTJunta {n : ℕ} (f : Qubits n → Bool) (T : Finset (Fin n)) : Prop :=
  ∀ x y : Qubits n, (∀ i ∈ T, x i = y i) → f x = f y

/-- **Definition 2.13** (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…, p.16):
`f ∈ ℬ^{(n)}_k = ⋃_{|T| ≤ k} ℬ^{(n)}_T`, i.e. `f` is a `k`-junta.

**Formalization Note** The paper restricts to `0 ≤ k ≤ n`; for `k > n` the class is all functions,
and no statement of this mission uses `k > n` outside the paper's range. -/
def IsJunta {n : ℕ} (f : Qubits n → Bool) (k : ℕ) : Prop :=
  ∃ T : Finset (Fin n), T.card ≤ k ∧ IsTJunta f T

/-- **Definition 2.14** (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…, p.17):
the uniform Hamming distance `dist_ℬ(f, g) = Pr_{x ∼ Unif({0,1}^n)}[f(x) ≠ g(x)]`. -/
noncomputable def hdist {n : ℕ} (f g : Qubits n → Bool) : ℝ :=
  ((Finset.univ.filter fun x => f x ≠ g x).card : ℝ) / 2 ^ n

/-- **Definition 2.14** (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…, p.17):
`dist_ℬ(f, ℬ_T) = min_{g ∈ ℬ_T} dist_ℬ(f, g)`, the minimum over the finite set of `T`-juntas, which
is nonempty (it contains the constant function `0`). -/
noncomputable def distT {n : ℕ} (f : Qubits n → Bool) (T : Finset (Fin n)) : ℝ := by
  classical
  exact (Finset.univ.filter fun g : Qubits n → Bool => IsTJunta g T).inf'
    ⟨fun _ => false, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun _ _ _ => rfl⟩⟩ (hdist f)

/-- `f` is `ε`-far from `ℬ_k` (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…,
p.16: "ε-far from a junta class if its distance to that class … is at least ε"; Definition 2.14):
`dist_ℬ(f, ℬ_k) ≥ ε`.

**Formalization Note** `dist_ℬ(f, ℬ_k)` is a minimum over a finite nonempty set (constants are
`k`-juntas), so it is `≥ ε` exactly when `dist_ℬ(f, g) ≥ ε` for every `k`-junta `g`; this is the
form used. -/
def IsFar {n : ℕ} (f : Qubits n → Bool) (k : ℕ) (ε : ℝ) : Prop :=
  ∀ g : Qubits n → Bool, IsJunta g k → ε ≤ hdist f g

end OptQJunta


