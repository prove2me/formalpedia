-- Prove2me | Definitions.Def_ExpanderBIS_RandomHardCore_Setting
-- name    : ExpanderBIS_RandomHardCore_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T04:33:04.429312+00:00
-- url     : https://prove2.me/theorems/785cd7b4-1b13-40ac-b4f1-8259e0f06604
-- title:
--   Hard-core partition function, random regular bipartite graphs, and tiny polymers
-- statement:
--   Fix two labelled sides of size $m$ each. This file defines the finite family $\mathcal G^{\mathrm{bip}}(m,\Delta)$ of simple $\Delta$-regular bipartite graphs on those sides, the vertex boundary $\partial S$, bipartite $(\sigma,\rho)$-expansion, and the paper's standard expansion parameters. A set is tiny when $|S|\le (4\log\Delta/\Delta)m$.
--
--   For each side, a polymer is a nonempty tiny set connected in $G^2$; its weight is $w_\gamma=\lambda^{|\gamma|}/(1+\lambda)^{|\partial\gamma|}$. The file defines compatibility by graph distance greater than two, the polymer partition functions $\Xi^{\mathcal E}$ and $\Xi^{\mathcal O}$, and the hard-core partition function
--
--   $$Z_G(\lambda)=\sum_{I\text{ independent}}\lambda^{|I|}.$$
--
--   It uses the exponential relative approximation predicate from the shared Potts Setting. It defines the decay function $g(\gamma)=|\gamma|\Delta\log(1+\lambda)/(10\log\Delta)$, entropy in bits, and the limiting fraction of regular bipartite graphs satisfying a property. These definitions give all milestone statements one common model.
--
--   **Formalization Note** The random graph model uses two fixed labelled sides. Extended graph distance makes distinct components infinitely far apart. Connectedness makes polymers nonempty; the empty polymer family still contributes one to each partition function.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, pp. 1, 3, 8, 12, 18–19, 23–25, Definitions 10, 19, 21 and §§1, 4.1, 4.4–4.5

import Mathlib
import Definitions.Def_ExpanderBIS_Potts_Setting

open Classical Filter

namespace ExpanderBIS.RandomHardCore

noncomputable section

abbrev Vertex (m : ℕ) := Fin m ⊕ Fin m

def oddSide (m : ℕ) : Finset (Vertex m) :=
  Finset.univ.filter (fun v => match v with | .inl _ => true | .inr _ => false)

def evenSide (m : ℕ) : Finset (Vertex m) :=
  Finset.univ.filter (fun v => match v with | .inl _ => false | .inr _ => true)

def IsBipReg {m : ℕ} (G : SimpleGraph (Vertex m)) (Δ : ℕ) : Prop :=
  (∀ u v, G.Adj u v → (u ∈ oddSide m ↔ v ∈ evenSide m)) ∧
    ∀ v, G.degree v = Δ

noncomputable def Gbip (m Δ : ℕ) : Finset (SimpleGraph (Vertex m)) :=
  Finset.univ.filter (fun G => IsBipReg G Δ)

def vertexBoundary {m : ℕ} (G : SimpleGraph (Vertex m))
    (S : Finset (Vertex m)) : Finset (Vertex m) :=
  Finset.univ.filter (fun v => v ∉ S ∧ ∃ u ∈ S, G.Adj u v)

def IsSigmaRhoExpander {m : ℕ} (G : SimpleGraph (Vertex m))
    (σ ρ : ℝ) : Prop :=
  ∀ S : Finset (Vertex m),
    (S ⊆ oddSide m ∨ S ⊆ evenSide m) →
    (S.card : ℝ) ≤ σ * m →
    ρ * S.card ≤ (vertexBoundary G S).card

def IsStdExpander {m : ℕ} (G : SimpleGraph (Vertex m)) (Δ : ℕ) : Prop :=
  IsSigmaRhoExpander G (4 * Real.log Δ / Δ)
    ((Δ : ℝ) / (4 * Real.log Δ) - 1 / 2)

def IsTiny {m : ℕ} (Δ : ℕ) (S : Finset (Vertex m)) : Prop :=
  (S.card : ℝ) ≤ 4 * Real.log Δ / Δ * m

def powerTwo {m : ℕ} (G : SimpleGraph (Vertex m)) : SimpleGraph (Vertex m) where
  Adj u v := u ≠ v ∧ G.edist u v ≤ 2
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, by simpa [SimpleGraph.edist_comm] using h.2⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

def IsG2Connected {m : ℕ} (G : SimpleGraph (Vertex m))
    (S : Finset (Vertex m)) : Prop :=
  ((powerTwo G).induce (S : Set (Vertex m))).Connected

noncomputable def tinyPolymers {m : ℕ} (G : SimpleGraph (Vertex m))
    (Δ : ℕ) (side : Finset (Vertex m)) : Finset (Finset (Vertex m)) :=
  Finset.univ.filter (fun γ => γ ⊆ side ∧ IsTiny Δ γ ∧ IsG2Connected G γ)

def Compat2 {m : ℕ} (G : SimpleGraph (Vertex m))
    (γ η : Finset (Vertex m)) : Prop :=
  ∀ u ∈ γ, ∀ v ∈ η, (2 : ℕ∞) < G.edist u v

def hcWeight {m : ℕ} (G : SimpleGraph (Vertex m))
    (lam : ℝ) (γ : Finset (Vertex m)) : ℝ :=
  lam ^ γ.card / (1 + lam) ^ (vertexBoundary G γ).card

noncomputable def sideXi {m : ℕ} (G : SimpleGraph (Vertex m)) (Δ : ℕ)
    (side : Finset (Vertex m)) (lam : ℝ) : ℝ :=
  ∑ Γ ∈ (tinyPolymers G Δ side).powerset,
    if (∀ γ ∈ Γ, ∀ η ∈ Γ, γ ≠ η → Compat2 G γ η) then
      ∏ γ ∈ Γ, hcWeight G lam γ else 0

def IsIndependent {m : ℕ} (G : SimpleGraph (Vertex m))
    (I : Finset (Vertex m)) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v

noncomputable def hardcoreZ {m : ℕ} (G : SimpleGraph (Vertex m))
    (lam : ℝ) : ℝ :=
  ∑ I ∈ (Finset.univ : Finset (Finset (Vertex m))).filter (IsIndependent G),
    lam ^ I.card

def decay (Δ : ℕ) (lam : ℝ) {m : ℕ} (γ : Finset (Vertex m)) : ℝ :=
  γ.card * ((Δ : ℝ) / (10 * Real.log Δ)) * Real.log (1 + lam)

def H₂ (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

def AlmostEvery (Δ : ℕ)
    (P : ∀ m, SimpleGraph (Vertex m) → Prop) : Prop :=
  Filter.Tendsto
    (fun m => (((Gbip m Δ).filter (P m)).card : ℝ) / (Gbip m Δ).card)
    Filter.atTop (nhds 1)

def IsSparse {m : ℕ} (G : SimpleGraph (Vertex m)) (Δ : ℕ)
    (I : Finset (Vertex m)) : Prop :=
  ∀ side ∈ ({oddSide m, evenSide m} : Finset (Finset (Vertex m))),
    ∀ S : Finset (Vertex m), S ⊆ I ∩ side → IsG2Connected G S → IsTiny Δ S

end
end ExpanderBIS.RandomHardCore


