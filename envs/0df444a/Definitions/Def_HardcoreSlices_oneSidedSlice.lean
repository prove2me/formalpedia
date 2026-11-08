-- Prove2me | Definitions.Def_HardcoreSlices_oneSidedSlice
-- name    : HardcoreSlices_oneSidedSlice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:48.966742+00:00
-- url     : https://prove2.me/theorems/437ad59c-2f93-475f-a76a-ba9cf618e7a8
-- title:
--   The one-sided slice of the hardcore model
-- statement:
--   Let $G=(X,Y,E)$ be bipartite, $k\le|X|$ and $\lambda>0$. The law $\mu_\lambda^{(X,k)}$ on $\binom Xk$ is
--   $$\mu_\lambda^{(X,k)}(S)\propto\sum_{I\in\mathcal I(G),\,I\cap X=S}\lambda^{|I|},$$
--   with normalizing constant $Z_G^{(X,k)}(\lambda)$, and the complex is the downward closure of $\binom Xk$. The same holds with $Y$ in place of $X$. On $\binom Xk$ the weight has the closed form $\lambda^k(1+\lambda)^{|Y\setminus N(S)|}$.
--
--   The module also fixes the data of Lemma 5.1: the link vertices $\mathcal X_\tau(1)$, the sets $N_\tau(u)=N(u)\setminus N(\tau)$, and $\Delta_\tau=\mathbf E_{v\sim\mathcal X_\tau(1)}|N_\tau(v)|$ under the uniform measure.
--
--   **Formalization Note** The law is defined from the sum of Definition 1.7. The closed form is separate (`closedWeight`), as Lemma 6.2 uses it; the two agree on $\binom Xk$.
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Definition 1.7 and the closed form, p.3; Lemma 5.1, p.22

import Mathlib
import Definitions.Def_ExpanderBIS_RandomHardCore_Setting
import Definitions.Def_HardcoreSlices_downUp
import Definitions.Def_HardcoreSlices_IsThreshold
import Definitions.Def_HardcoreSlices_twoSidedSlice
import Definitions.Def_HDXConc_linkWeight

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- The weight `Σ_{I∈I(G), I∩X=S} λ^{|I|}` of a set `S` of one side. Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), Definition 1.7, p.3. `side` is `X` or `Y`
("resp."). -/
noncomputable def oneSidedWeight {m : ℕ} (G : SimpleGraph (Vertex m)) (lam : ℝ)
    (side S : Finset (Vertex m)) : ℝ :=
  ∑ I ∈ (Finset.univ : Finset (Finset (Vertex m))).filter
      (fun I => IsIndependent G I ∧ I ∩ side = S), lam ^ I.card

/-- The closed form `λ^k (1 + λ)^{|Y \ N(S)|}` of p.3 and of Lemma 6.2 (p.26). -/
noncomputable def closedWeight {m : ℕ} (G : SimpleGraph (Vertex m)) (lam : ℝ)
    (side : Finset (Vertex m)) (k : ℕ) (S : Finset (Vertex m)) : ℝ :=
  lam ^ k * (1 + lam) ^ (nonNbrs G side S).card

/-- The partition function `Z_G^{(X,k)}(λ)` of Definition 1.7, p.3. -/
noncomputable def oneSidedZ {m : ℕ} (G : SimpleGraph (Vertex m)) (lam : ℝ)
    (side : Finset (Vertex m)) (k : ℕ) : ℝ :=
  ∑ S ∈ side.powersetCard k, oneSidedWeight G lam side S

/-- The one-sided law `µ_λ^{(X,k)}` on `(X choose k)` (Definition 1.7, p.3), and `0` off that set. -/
noncomputable def oneSidedLaw {m : ℕ} (G : SimpleGraph (Vertex m)) (lam : ℝ)
    (side : Finset (Vertex m)) (k : ℕ) (S : Finset (Vertex m)) : ℝ :=
  if S ∈ side.powersetCard k then oneSidedWeight G lam side S / oneSidedZ G lam side k else 0

/-- The one-sided complex (Definition 1.7, p.3): "the downward closure of `(X choose k)`". -/
noncomputable def oneSidedComplex {m : ℕ} (side : Finset (Vertex m)) (k : ℕ) :
    Finset (Finset (Vertex m)) :=
  downClosure (side.powersetCard k)

/-- The vertices `Xτ(1)` of the link of `τ` in the one-sided complex. -/
noncomputable def oneSidedLink {m : ℕ} (side : Finset (Vertex m)) (k : ℕ) (τ : Finset (Vertex m)) :
    Finset (Vertex m) :=
  HDXConc.linkVerts (oneSidedComplex side k) τ

/-- `Nτ(u) = N(u) \ N(τ)` (p.9). -/
noncomputable def nbrTau {m : ℕ} (G : SimpleGraph (Vertex m)) (τ : Finset (Vertex m)) (u : Vertex m) :
    Finset (Vertex m) :=
  vertexBoundary G {u} \ vertexBoundary G τ

/-- `∆τ := E_{v∼Xτ(1)} |Nτ(v)|`, the expectation under the uniform measure on `Xτ(1)` (pp.22, 25). -/
noncomputable def deltaTau {m : ℕ} (G : SimpleGraph (Vertex m)) (side : Finset (Vertex m)) (k : ℕ)
    (τ : Finset (Vertex m)) : ℝ :=
  (∑ v ∈ oneSidedLink side k τ, ((nbrTau G τ v).card : ℝ)) / ((oneSidedLink side k τ).card : ℝ)

end HardcoreSlices


