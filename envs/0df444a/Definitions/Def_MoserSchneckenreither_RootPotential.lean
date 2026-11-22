-- Prove2me | Definitions.Def_MoserSchneckenreither_RootPotential
-- name    : MoserSchneckenreither_RootPotential
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T08:56:30.747081+00:00
-- url     : https://prove2.me/theorems/4b6c8889-e5c5-4112-89d5-77e5cbb8fb35
-- title:
--   Rootwise resource potential
-- statement:
--   A constructor-like root contributes its charge and the sum of its children’s potentials at their input annotations. Variables and unsupported roots have potential zero. The context potential sums the rootwise potentials of the assigned terms at the context annotations.
-- source:
--   Georg Moser and Manuel Schneckenreither, Automated amortised resource analysis for term rewrite systems, Science of Computer Programming 185 (2020), article 102306, https://doi.org/10.1016/j.scico.2019.102306. Proposed variation of Definition 3, p. 7, for the identity of Lemma 2, pp. 8–9.

import Definitions.Def_MoserSchneckenreither_Annotations

noncomputable section

namespace MoserSchneckenreither

variable {sig : Signature} {P : Problem sig}

/-- A rootwise variant of Definition 3. A constructor-like root contributes its charge
and the potentials of its children. A variable or unsupported root contributes zero. -/
def rootPotential (F : AnnotatedSignature P) : Term sig → Annotation → ℚ≥0
  | .var _, _ => 0
  | .app f ts, q => by
    classical
    exact if ConstructorLike P f then
      F.cost f q + (List.ofFn fun i ↦ rootPotential F (ts i) (F.input f q i)).sum
    else 0

/-- The sum of the rootwise potentials of the substitution images at the context annotations. -/
def rootContextPotential (F : AnnotatedSignature P) (σ : ℕ → Term sig) (Γ : Context) :
    ℚ≥0 := (Γ.map fun a ↦ rootPotential F (σ a.1) a.2).sum

end MoserSchneckenreither


