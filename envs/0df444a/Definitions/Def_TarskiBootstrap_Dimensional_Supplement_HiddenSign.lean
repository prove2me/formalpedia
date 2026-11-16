-- Prove2me | Definitions.Def_TarskiBootstrap_Dimensional_Supplement_HiddenSign
-- name    : TarskiBootstrap_Dimensional_Supplement_HiddenSign
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:03:48.437192+00:00
-- url     : https://prove2.me/theorems/6ab5ac2f-0f9f-4a9f-a33f-fa0e7f3042ac
-- title:
--   Hidden-sign constructor $H_s$, Tarski$^H$ and $K_3\otimes\Gamma_0$
-- statement:
--   Let $A\subseteq[n]^k$ and let $D=\{y:\exists x\in A,\ y\preceq x\}$ be its downward closure. For $s\in\{-1,0,1\}$ and a self-map $f$ with fixed point $f^*$, the **hidden sign function** is
--
--   $$
--   \sigma^f_s(x)=\begin{cases}s,& x=f^*,\\ -1,& x\ne f^*,\ x\in D,\\ 1,& x\notin D,\end{cases}
--   $$
--
--   and the **hidden-sign constructor** is $H_s(f)=(f,\sigma^f_s)$, whose oracle returns $(f(x),\sigma^f_s(x))$. The **hidden-sign problem** maps a Tarski$^*$ instance to $\mathrm{Tarski}^H(n,k):(f,\sigma)\mapsto\sigma(f^*)$. The family $\mathcal F'=H_{-1}(\mathcal F)\sqcup H_0(\mathcal F)\sqcup H_1(\mathcal F)$ is labelled by $(s,f)\in\{-1,0,1\}\times\mathcal F$. With $K_3$ the adjacency matrix of a triangle on $\{-1,0,1\}$ ($0$ on the diagonal, $1$ elsewhere), the adversary matrix is
--
--   $$
--   \Gamma=K_3\otimes\Gamma_0,\qquad \Gamma[(s_1,f_1),(s_2,f_2)]=K_3[s_1,s_2]\,\Gamma_0[f_1,f_2].
--   $$
--
--   These are the objects of Section 4.1, used to compose Tarski with ordered search.
--
--   **Formalization Note** $f^*$ is the published `fixedPoint f`. The answer $\sigma(f^*)$ is read off the oracle string $x\mapsto(f(x),\sigma(x))$, and $\mathcal F'$ is also provided as the set of these oracle strings, for use with $\mathrm{SA}$. The Kronecker product is Mathlib's `⊗ₖ`, indexed by `SignType × F`.
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Definition 4.2, equations (4.1)–(4.4), PDF/printed pp. 17–18, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. Printed page = PDF page. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_FixedPoint
import Definitions.Def_TarskiBootstrap_Dimensional_DownwardClosure

open scoped Matrix Kronecker

namespace TarskiBootstrap.Dimensional.Supplement

/-- The hidden sign function `σ_s^f` of (4.2), PDF/printed p. 17: `s` at `x = f*`,
`-1` at `x ≠ f*` in the downward closure `D` of the antichain `A`, and `1` outside `D`. -/
noncomputable def hiddenSign {n k : ℕ+} (A : Set (Grid n k)) (s : SignType)
    (f : Grid n k → Grid n k) (x : Grid n k) : SignType := by
  classical
  exact if x = fixedPoint f then s else if x ∈ downwardClosure A then -1 else 1

/-- The oracle of the `Tarski*` instance `H_s(f) = (f, σ_s^f)` of Definition 4.2:
at `x` it returns `(f(x), σ_s^f(x))`. -/
noncomputable def hiddenSignOracle {n k : ℕ+} (A : Set (Grid n k)) (s : SignType)
    (f : Grid n k → Grid n k) : Grid n k → Grid n k × SignType :=
  fun x => (f x, hiddenSign A s f x)

/-- The hidden-sign problem (4.1), p. 17: `Tarski^H(n, k) : (f, σ) ↦ σ(f*)`, read off
the oracle string `x ↦ (f(x), σ(x))`. -/
noncomputable def tarskiHAnswer {n k : ℕ+} (y : Grid n k → Grid n k × SignType) :
    SignType :=
  (y (fixedPoint (fun z => (y z).1))).2

/-- The family `F′ = H_{-1}(F) ⊔ H_0(F) ⊔ H_1(F)` of (4.3), p. 18, as oracle strings. -/
noncomputable def hiddenSignFamily {n k : ℕ+} (A : Set (Grid n k))
    (F : Set (Grid n k → Grid n k)) : Set (Grid n k → Grid n k × SignType) :=
  Set.range (fun p : SignType × F => hiddenSignOracle A p.1 p.2.val)

/-- `K_3`, the adjacency matrix of a triangle on `{-1, 0, 1}`, (4.4), p. 18. -/
def triangleMatrix : Matrix SignType SignType ℝ :=
  fun a b => if a = b then 0 else 1

/-- `Γ = K_3 ⊗ Γ_0` of (4.4), p. 18, indexed by the labels `(s, f)` of `F′`:
`Γ[(s₁, f₁), (s₂, f₂)] = K_3[s₁, s₂] · Γ_0[f₁, f₂]`. -/
def hiddenSignAdversary {S : Type*} (Γ₀ : Matrix S S ℝ) :
    Matrix (SignType × S) (SignType × S) ℝ :=
  triangleMatrix ⊗ₖ Γ₀

end TarskiBootstrap.Dimensional.Supplement


