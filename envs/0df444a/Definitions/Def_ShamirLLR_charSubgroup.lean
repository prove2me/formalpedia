-- Prove2me | Definitions.Def_ShamirLLR_charSubgroup
-- name    : ShamirLLR_charSubgroup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:27:27.627362+00:00
-- url     : https://prove2.me/theorems/ff3a5238-b360-4284-9602-ff0a16a35ced
-- title:
--   Character subgroup $H$, commutator subgroup $Z=[H,H]$ and rationality
-- statement:
--   For first-level characters $\xi_j=k_j\cdot\psi_1$ on $G$, the common kernel of their differentials is $\mathfrak h=\bigcap_j\ker d\xi_j\subseteq\mathrm{Lie}(G)$, with $d\xi_j(v)=\sum_l(k_j)_lv_l$, and
--   $$
--   H=\exp(\mathfrak h)=\{x\in G:\ \xi_j(x)=0\ \text{for all } j\},\qquad Z=[H,H]=\exp([\mathfrak h,\mathfrak h]),
--   $$
--   where $[\mathfrak h,\mathfrak h]=\mathrm{span}_{\mathbb R}\{[v,w]:v,w\in\mathfrak h\}$. A connected subgroup is **rational** when its Lie algebra has a basis of rational combinations of the adapted Mal'cev basis.
--
--   These are the groups of the local reduction to a quadratic torus.
--
--   **Formalization Note** Lie algebras are subspaces of $\mathbb R^{d_G}$ in basis coordinates; $\exp$ of a central vector is the matrix exponential `LSS.mexp`.
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Lemma 7.3, p.50, and proof, p.52; §3.4, Eq. (20)–(21), p.22; §3.6, p.25 (PDF pp.51, 53, 23, 26)

import Mathlib
import Definitions.Def_LSSNil
import Definitions.Def_ShamirLLR_nilCoords

set_option autoImplicit false

namespace ShamirLLR

/-- For a finite family of first-level characters `ξ_j = k_j · ψ₁`, the Lie algebra
`⋂_j ker dξ_j ⊆ Lie(G)` in basis coordinates: `dξ_j(v) = ∑_l (k_j)_l v_l` (Eq. (20), p.22;
Lemma 7.3, p.50; "The Lie algebra of H consists of the vectors whose first-level coordinates lie
in ker C", p.52).

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
§3.4, pp.21–22; Lemma 7.3, p.50. -/
noncomputable def charLie (G : LSS.Nilmanifold 2) {J : Type*} [Fintype J]
    (k : J → Fin G.d → ℤ) : Submodule ℝ (Fin G.d → ℝ) :=
  LinearMap.ker (Matrix.mulVecLin (fun j l => (k j l : ℝ)))

/-- The subgroup `H = exp(⋂_j ker dξ_j) = {x ∈ G : ξ_j(x) = 0 for all j}` of Lemma 7.3, p.50.

**Formalization Note.** For first-level rows `k_j`, `ξ_j(exp v) = dξ_j(v)` and `ψ₁` is additive
(p.22), so `exp(⋂_j ker dξ_j)` is the set of `x ∈ G` with `k_j · ψ₁(x) = 0` for all `j`. -/
noncomputable def charSubgroup (G : LSS.Nilmanifold 2) {J : Type*} (k : J → Fin G.d → ℤ) :
    Set G.Mat :=
  {x | G.Mem x ∧ ∀ j, charVal G (k j) x = 0}

/-- The commutator algebra `𝔠 = [𝔥, 𝔥] = span_ℝ{[v, w] : v, w ∈ 𝔥}` of `𝔥 = Lie(H)`
(proof of Lemma 7.3, Step 3, p.52). -/
noncomputable def brSpan (G : LSS.Nilmanifold 2) {J : Type*} [Fintype J]
    (k : J → Fin G.d → ℤ) : Submodule ℝ (Fin G.d → ℝ) :=
  Submodule.span ℝ {u | ∃ v ∈ charLie G k, ∃ w ∈ charLie G k, u = lieBr G v w}

/-- The commutator subgroup `Z = [H, H] = exp(𝔠)` of Lemma 7.3 (p.50; "Z = [H, H] = exp(𝔠)",
p.52). -/
noncomputable def commSubgroup (G : LSS.Nilmanifold 2) {J : Type*} [Fintype J]
    (k : J → Fin G.d → ℤ) : Set G.Mat :=
  {x | ∃ u ∈ brSpan G k, x = LSS.mexp (∑ c, u c • G.X c)}

/-- A connected subgroup with Lie algebra `S` (in basis coordinates) is rational: `S` has a basis
of vectors with rational coordinates in the adapted Mal'cev basis (§3.6, p.25: "In coordinates,
this means that Lie(H) has a basis Y₁, …, Y_{dim H} that are rational linear combinations of the
adapted Mal'cev basis"). -/
def IsRationalLie (G : LSS.Nilmanifold 2) (S : Submodule ℝ (Fin G.d → ℝ)) : Prop :=
  ∃ (n : ℕ) (b : Fin n → Fin G.d → ℚ),
    LinearIndependent ℝ (fun i j => (b i j : ℝ)) ∧
      Submodule.span ℝ (Set.range fun i j => (b i j : ℝ)) = S

end ShamirLLR


