-- Prove2me | Definitions.Def_MinCostMaj_CUGReducesTo
-- name    : MinCostMaj_CUGReducesTo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:28:10.673535+00:00
-- url     : https://prove2.me/theorems/135ddb25-5fba-4fd5-b63f-35c0d0a122b1
-- title:
--   $\mathrm{cUG}(k)$ reduces to $\mathrm{MinCostCSP}(\mathbf A)$
-- statement:
--   Weighted $\mathrm{cUG}(k)$ **reduces** to $\mathrm{MinCostCSP}(\mathbf A)$ if there are polynomial-time maps $\Phi$ and $\Psi$ and a constant $c$ such that, for every $\mathrm{cUG}(k)$ instance $G$:
--
--   1. $\Phi(G)$ is an instance of $\mathrm{MinCostCSP}(\mathbf A)$ that has a solution of finite cost, and $\mathrm{OPT}(\Phi(G))\le c\cdot\mathrm{OPT}(G)$;
--   2. for every solution $\alpha$ of $\Phi(G)$, $\Psi(G,\alpha)$ is an assignment $\beta$ of $G$ with $\mathrm{cost}_G(\beta)\le c\cdot\mathrm{cost}(\alpha)$.
--
--   Composed with a $C$-approximation of $\mathrm{MinCostCSP}(\mathbf A)$ this gives a $c^2C$-approximation of $\mathrm{cUG}(k)$, so constant-factor approximability transfers from $\mathrm{MinCostCSP}(\mathbf A)$ to $\mathrm{cUG}(k)$. This is the second alternative of the main theorem; §4.1 builds such reductions from gadgets ("approximation-preserving, up to the fixed gadget constant").
--
--   **Formalization Note** Both maps are Mathlib `Turing.TM2ComputableInPolyTime` functions on the fixed binary encodings. The target is $\mathrm{MinCostCSP}$ of the given structure $\mathbf A$, not of an expansion.
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Theorem 1.1, p.4; §4.1, pp.8–10 (PDF pp.5, 9–11)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_MinCostMaj_Struct
import Definitions.Def_MinCostMaj_MCInst
import Definitions.Def_MinCostMaj_CUGInst
import Definitions.Def_MinCostMaj_encInst

namespace MinCostMaj

open scoped ENNReal

/-- **cUG(k) reduces to MinCostCSP(A)** (approximation-preserving polynomial-time reduction).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Theorem 1.1, second bullet, p.4 ("a fixed-alphabet cyclic Unique
Games deletion problem reduces to MinCostCSP(A)"), and §4.1, pp.8–10 ("the reduction is
approximation-preserving, up to the fixed gadget constant").

There are polynomial-time maps `Φ` (cUG(k) instance ↦ MinCostCSP(A) instance) and `Ψ` (cUG
instance and a solution of its image ↦ cUG assignment) and a constant `c` such that, for every
well-formed weighted cUG(k) instance `G`: `Φ G` is a well-formed instance with a finite-cost
solution and `OPT(Φ G) ≤ c · OPT(G)`; and every solution `α` of `Φ G` is mapped by `Ψ` to an
assignment `β` of `G` with `cost_G(β) ≤ c · cost(α)`.

**Formalization Note.** "Reduces" is read as this cost reduction with both maps in Mathlib's
`Turing.TM2ComputableInPolyTime` (inputs and outputs in the fixed binary encodings `encCUG`,
`encInst`, `encCUGSol`, `encList`). Arcs carry positive rational weights, which contain unit
weights (footnote 2, p.4). Composing with any `C`-approximation of MinCostCSP(A) gives a
`c²C`-approximation of cUG(k). The target is MinCostCSP of the given structure `A` itself. -/
def CUGReducesTo (k : ℕ) {d : ℕ} (A : Struct d) : Prop :=
  ∃ (Φ : CUGInst → MCInst) (Ψ : CUGInst × List ℕ → List ℕ) (c : ℝ),
    Nonempty (Turing.TM2ComputableInPolyTime encCUG encInst Φ) ∧
    Nonempty (Turing.TM2ComputableInPolyTime encCUGSol encList Ψ) ∧
    ∀ G : CUGInst, G.WellFormed →
      (Φ G).WellFormed A ∧
      (∃ α : Fin (Φ G).n → Fin d, (Φ G).IsSolution A α ∧ (Φ G).costOf α < ⊤) ∧
      (Φ G).OPT A ≤ ENNReal.ofReal (c * G.OPT k) ∧
      ∀ α : Fin (Φ G).n → Fin d, (Φ G).IsSolution A α →
        ∃ β : Fin G.n → Fin k,
          Ψ (G, List.ofFn (fun x => (α x : ℕ))) = List.ofFn (fun u => (β u : ℕ)) ∧
          ENNReal.ofReal (G.cost k β) ≤ ENNReal.ofReal c * (Φ G).costOf α

end MinCostMaj


