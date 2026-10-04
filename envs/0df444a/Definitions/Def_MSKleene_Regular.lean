-- Prove2me | Definitions.Def_MSKleene_Regular
-- name    : MSKleene_Regular
-- status  : Definition
-- author  : @Cosme
-- created : 2026-09-08T12:28:45.302745+00:00
-- url     : https://prove2.me/theorems/33e8c82f-b122-4fb9-a3fc-eac4f3d77453
-- title:
--   The $s$-regular languages $\mathrm{Reg}_s(\mathbf{T}_\Sigma(X))$
-- statement:
--   The **$s$-regular languages** of the free many-sorted algebra (Definition 4.6).
--
--   A language `L ⊆ T_Σ(X)_s` is **$s$-regular** (`sRegular sig X s L`) when there is a finite $S$-sorted set $Z \supseteq X$ and a regular expression `R` of type `s` over $(S,\Sigma,Z)$ with
--   $$L = \{R\}^{Z\sharp}_s$$
--   as subsets of $\mathrm{T}_\Sigma(Z)_s$. The extension $Z \supseteq X$ is modelled as $Z_s = X_s \oplus E_s$ for an $S$-sorted set `E` of auxiliary variables (`extVars`), with the canonical inclusion `Sum.inl` (`extIncl`); `L` is transported into $\mathrm{T}_\Sigma(Z)_s$ by relabelling along that inclusion.
--
--   `RegS sig X s` collects the $s$-regular languages; this is $\mathrm{Reg}_s(\mathbf{T}_\Sigma(X))$, one side of the mission goal.
--
--   **Formalization Note** The auxiliary variables of $Z - X$ play a purely bookkeeping role: they carry the iteration and substitution steps and vanish when the regular expression is interpreted as a language.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026, https://arxiv.org/abs/1808.08217 (predecessor CVCL20)

/-
The `s`-regular languages of the free many-sorted algebra (Definition 4.6).

`L ⊆ T_Σ(X)_s` is **`s`-regular** when there is a finite `S`-sorted set `Z ⊇ X`
and a regular expression `R` of type `s` over `(S,Σ,Z)` with `L = {R}^{Z♯}_s`
(the equality taken inside `T_Σ(Z)_s`).

Here the extension `Z ⊇ X` is modelled as `Z_s = X_s ⊕ E_s` for an `S`-sorted
set `E` of auxiliary variables, with the canonical inclusion `Sum.inl`; `L` is
transported into `T_Σ(Z)_s` by relabelling along that inclusion.
-/
import Definitions.Def_MSKleene_RegAlgebra
import Definitions.Def_MSKleene_Recognizable
import Mathlib.Data.Set.Image

namespace MSKleene

universe u

variable {S : Type u} {sig : Signature S} {X : SSet S}

/-- The `S`-sorted set `X` extended by the auxiliary variables `E`. -/
def extVars (X E : SSet S) : SSet S := fun s => X s ⊕ E s

/-- The canonical inclusion `X ↪ X ⊕ E`. -/
def extIncl (X E : SSet S) : SMap X (extVars X E) := fun _ x => Sum.inl x

/-- `L ⊆ T_Σ(X)_s` is **`s`-regular** (Definition 4.6). -/
def sRegular (sig : Signature S) (X : SSet S) (s : S) (L : Set (Term sig X s)) :
    Prop :=
  ∃ E : SSet S, SFinite (extVars X E) ∧
    ∃ R : RegExpr sig (extVars X E) s,
      interpExpr sig (extVars X E) s R
        = (fun t : Term sig X s => Term.relabel (extIncl X E) t) '' L

/-- `Reg_s(𝐓_Σ(X))` — the set of `s`-regular languages of `T_Σ(X)` at sort `s`. -/
def RegS (sig : Signature S) (X : SSet S) (s : S) : Set (Set (Term sig X s)) :=
  { L | sRegular sig X s L }

end MSKleene


