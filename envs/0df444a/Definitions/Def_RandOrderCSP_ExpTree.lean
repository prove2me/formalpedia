-- Prove2me | Definitions.Def_RandOrderCSP_ExpTree
-- name    : RandOrderCSP_ExpTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:09:05.260616+00:00
-- url     : https://prove2.me/theorems/a1257c67-0490-4314-b6c4-4539d66614fe
-- title:
--   Exploration trees and $\text{Rand-Exp-Type}_R$
-- statement:
--   An **$R$-exploration tree** in $H$ labels the words $w\in[k]^{<R}$ by edges $j_T(w)$ so that for each $(u,\ell)\in[k]^{<R}$ the vertex $v_T(u,\ell)=M_H(j_T(u),\ell)$ lies on $j_T(u,\ell)$. Algorithm 1 samples $j_T(())$ uniformly and then each $j_T(u,\ell)$ uniformly from the edges at $v_T(u,\ell)$, so
--
--   $$\mathbb P_{\text{Rand-Exp}_R(H)}[T]=\frac1{m_H}\prod_{w\ne()}\frac1{\deg_H(v_T(w))}.$$
--
--   $\mathrm{type}(T)$ is the isomorphism class of the subhypergraph $H[T]$ with each edge $j$ colored $(f_T(j),A_T(j))$, where $A_T(j)=\{w:j_T(w)=j\}$. $\mathcal E_{R,\Gamma}$ is the set of all such types, and $\text{Rand-Exp-Type}_R(\Phi)$ is the law of $\mathrm{type}(T)$.
--
--   **Formalization Note** The law of Algorithm 1 is defined by the product formula of Lemma 10.11, which is the chain rule for the algorithm.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), §10.2, pp.52–54

import Mathlib
import Definitions.Def_RandOrderCSP_typeR

namespace RandOrderCSP

/-- `[k]^{<R}` (§10.2, p.52): the words of length less than `R`, with `( )` the empty list and `(w, ℓ)`
the list `w ++ [ℓ]`. -/
abbrev Word (k R : ℕ) : Type := {w : List (Fin k) // w.length < R}

instance (k R : ℕ) : Finite (Word k R) :=
  (List.finite_length_lt (Fin k) R).to_subtype

noncomputable instance (k R : ℕ) : Fintype (Word k R) := Fintype.ofFinite _

variable {k : ℕ} {V E Col : Type}

/-- **An `R`-exploration tree** (§10.2, p.52).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), p.52: `T = (j_T : [k]^{<R} → ℰ_H, v_T)` with
"∀u ∈ [k]^{<R−1}, ℓ ∈ [k], v_T(u, ℓ) = M_H(j_T(u), ℓ) ∈ 𝒱_H(j_T(u, ℓ))" (10.8).

**Formalization Note.** The edge labels determine the vertex labels (p.52), so `T` is the function
`j_T` with (10.8) as its property; `v_T(u, ℓ)` is `H.M (j_T u) ℓ`. -/
abbrev ExpTree (H : Hypergraph k V E) (R : ℕ) : Type :=
  {j : Word k R → E // ∀ (u : List (Fin k)) (ℓ : Fin k) (h : (u ++ [ℓ]).length < R),
    ∃ ℓ', H.M (j ⟨u, by simp at h; omega⟩) ℓ = H.M (j ⟨u ++ [ℓ], h⟩) ℓ'}

noncomputable instance [Finite E] (H : Hypergraph k V E) (R : ℕ) : Fintype (ExpTree H R) :=
  Fintype.ofFinite _

/-- The non-root nodes of the tree, as pairs `(u, ℓ)` with `(u, ℓ) ∈ [k]^{<R}`. -/
abbrev ChildNode (k R : ℕ) : Type := {p : List (Fin k) × Fin k // (p.1 ++ [p.2]).length < R}

noncomputable instance (k R : ℕ) : Fintype (ChildNode k R) :=
  haveI : Finite (ChildNode k R) :=
    Finite.of_injective
      (fun p : ChildNode k R => ((⟨p.1.1, by have := p.2; simp at this; omega⟩ : Word k R), p.1.2))
      (fun p p' h => by
        simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
        exact Subtype.ext (Prod.ext h.1 h.2))
  Fintype.ofFinite _

/-- `P_{Rand-Exp_R(H)}[T] = (1/m_H) ∏_{w ∈ [k]^{<R} \ {( )}} 1/deg_H(v_T(w))`.

**Formalization Note.** The paper defines `Rand-Exp_R(H)` by Algorithm 1 (p.53): sample `j_T(( ))`
uniformly, then for each `w = (u, ℓ)` sample `j_T(w)` uniformly from the edges incident to
`v_T(w) = M_H(j_T(u), ℓ)`. Its law is this product by the chain rule (Lemma 10.11, p.54). -/
noncomputable def expTreeProb [Fintype V] [DecidableEq V] [Fintype E] (H : Hypergraph k V E) {R : ℕ}
    (T : ExpTree H R) : ℝ :=
  (1 / (Fintype.card E : ℝ)) *
    ∏ p : ChildNode k R,
      1 / (H.deg (H.M (T.1 ⟨p.1.1, by have := p.2; simp at this; omega⟩) p.1.2) : ℝ)

/-- The colored hypergraph `H[T]` (p.52) in which each edge `j` receives the color
`(f_T(j), A_T(j))`, with `A_T(j) = {w : j_T(w) = j}` (p.54). -/
noncomputable def expTreeHG [Finite V] [Finite E] (H : Hypergraph k V E) (f : E → Col) {R : ℕ}
    (T : ExpTree H R) : ColoredHG k (Col × Set (Word k R)) where
  V := {v // ∃ w ℓ, H.M (T.1 w) ℓ = v}
  E := {i // ∃ w, T.1 w = i}
  fV := Fintype.ofFinite _
  fE := Fintype.ofFinite _
  H :=
    { M := fun i ℓ => ⟨H.M i.1 ℓ, by
        obtain ⟨w, hw⟩ := i.2
        exact ⟨w, ℓ, by rw [hw]⟩⟩
      row_inj := fun i _ _ h => H.row_inj i.1 (congrArg Subtype.val h) }
  col := fun i => (f i.1, {w | T.1 w = i.1})

/-- `type(T)` (p.54): "the isomorphism class of the colored hypergraph H[T] in which each edge j
receives the color (f_T(j), A_T(j))." -/
noncomputable def expType [Finite V] [Finite E] (H : Hypergraph k V E) (f : E → Col) {R : ℕ}
    (T : ExpTree H R) : ColorClass k (Col × Set (Word k R)) :=
  Quotient.mk (ColoredHG.setoid k _) (expTreeHG H f T)

/-- **`ℰ_{R,Γ}`** (p.54): "the set of types of Γ-colored R-exploration trees". The paper notes that this
set is finite (footnote 9). -/
def expTypes (k R : ℕ) (Col : Type) : Set (ColorClass k (Col × Set (Word k R))) :=
  {τ | ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (H : Hypergraph k V E) (f : E → Col)
    (T : ExpTree H R), expType H f T = τ}

/-- **`Rand-Exp-Type_R(Φ)`** (p.54): the distribution over `ℰ_{R,Γ}` of `type(T)` when
`T ∼ Rand-Exp_R(Φ)`. -/
noncomputable def expTypeLaw [Fintype V] [DecidableEq V] [Fintype E] (H : Hypergraph k V E)
    (f : E → Col) (R : ℕ) (τ : expTypes k R Col) : ℝ := by
  classical
  exact ∑ T : ExpTree H R, if expType H f T = τ.1 then expTreeProb H T else 0

end RandOrderCSP


