-- Prove2me | Definitions.Def_NishtAbel2024_ComparisonCoherenceAux
-- name    : NishtAbel2024_ComparisonCoherenceAux
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-01T21:57:29.113227+00:00
-- url     : https://prove2.me/theorems/caa3c74d-f906-4149-90fc-223330db92fb
-- title:
--   Occurrence transport for size comparison
-- statement:
--   For the existing NishtAbel2024 comparison judgments, define mutually inductive guarded type and branch comparisons. Their rules follow the existing comparisons, with one extra condition at each extensional comparison: every occurrence of the selected variable recognized by the existing SizeOccursFixPol judgment in the opened right operand must transport to a recognized occurrence with the same fixpoint kind and polarity in the original right operand. The guard is parameterized by the size variable and is checked recursively. This is an auxiliary sufficient condition; its derivability from source inference is not established.
-- source:
--   Auxiliary guard for the current Lean formalization, inspired by Kanstantsin Nisht, Type-Based Termination Checking in Agda (master’s thesis supervised by Andreas Abel, 2024), https://knisht.github.io/agda/msc.pdf, §6.3.3–6.3.4, pp. 51–52. This exact guard is an additional condition not stated as a theorem of the thesis; whether source-generated comparisons satisfy it is unproved.

import Definitions.Def_NishtAbel2024_Inference

namespace NishtAbel2024

mutual

inductive CoherentCompareTypes (i : SizeVar) (Φ : FlexVars) :
    KindingCtx → SKind → Polarity → TypeExpr → TypeExpr → List SizeConstraint → Prop where
  | atom (Δ : KindingCtx) (ι : SKind) (π : Polarity) (K : TyAtom) :
      CoherentCompareTypes i Φ Δ ι π (.atom K) (.atom K) []
  | app {Δ : KindingCtx} {π₁ π : Polarity} {ι₁ ι₂ : SKind}
      {F F' G G' : TypeExpr} {C₁ C₂ : List SizeConstraint} :
      KindInfer Δ F' (.arr π₁ (Kind.ofSKind ι₁) (Kind.ofSKind ι₂)) →
      CoherentCompareTypes i Φ Δ (.arr π₁ ι₁ ι₂) π F F' C₁ →
      CoherentCompareTypes i Φ (Δ.invScalePol π₁) ι₁ (Polarity.comp π₁ π) G G' C₂ →
      CoherentCompareTypes i Φ Δ ι₂ π (.app F G) (.app F' G') (C₁ ++ C₂)
  | lam {Δ : KindingCtx} {π₁ π : Polarity} {ι₁ ι₂ : SKind}
      {F F' : TypeExpr} {X : TyVar} {C : List SizeConstraint} :
      (∀ fk q, SizeOccursFixPol (Δ.extType X π₁ (Kind.ofSKind ι₁)) fk i q
          (F'.normApp (.atom (.var X))) → SizeOccursFixPol Δ fk i q F') →
      CoherentCompareTypes i Φ (Δ.extType X π₁ (Kind.ofSKind ι₁)) ι₂ π
        (F.normApp (.atom (.var X))) (F'.normApp (.atom (.var X))) C →
      CoherentCompareTypes i Φ Δ (.arr π₁ ι₁ ι₂) π F F' C
  | mu {Δ : KindingCtx} {π π₁ π₂ : Polarity} {a b : SizeExp}
      {S S' : List (ConsName × TypeExpr)} {C : List SizeConstraint} :
      Φ.lookupSizePol .pos a = some π₁ →
      Φ.lookupSizePol .pos b = some π₂ →
      CoherentCompareBranches i Φ Δ π S S' C →
      CoherentCompareTypes i Φ Δ .star π (.mu a S) (.mu b S')
        (SizeConstraint.ofPol (Polarity.comp (Polarity.infoMax π₁ π₂) π) a b ++ C)
  | nu {Δ : KindingCtx} {π π₁ π₂ : Polarity} {a b : SizeExp}
      {R R' : List (ProjName × TypeExpr)} {C : List SizeConstraint} :
      Φ.lookupSizePol .neg a = some π₁ →
      Φ.lookupSizePol .neg b = some π₂ →
      CoherentCompareBranches i Φ Δ π R R' C →
      CoherentCompareTypes i Φ Δ .star π (.nu a R) (.nu b R')
        (SizeConstraint.ofPol (Polarity.comp (Polarity.infoMax π₁ π₂) π) a b ++ C)

inductive CoherentCompareBranches (i : SizeVar) (Φ : FlexVars) :
    KindingCtx → Polarity → List (Nat × TypeExpr) → List (Nat × TypeExpr) →
      List SizeConstraint → Prop where
  | nil (Δ : KindingCtx) (π : Polarity) :
      CoherentCompareBranches i Φ Δ π [] [] []
  | cons {Δ : KindingCtx} {π : Polarity} {nm : Nat} {F F' : TypeExpr}
      {rest rest' : List (Nat × TypeExpr)} {C₁ C₂ : List SizeConstraint} :
      CoherentCompareTypes i Φ Δ fwFunctorSKind π F F' C₁ →
      CoherentCompareBranches i Φ Δ π rest rest' C₂ →
      CoherentCompareBranches i Φ Δ π ((nm, F) :: rest) ((nm, F') :: rest') (C₁ ++ C₂)

end

end NishtAbel2024


