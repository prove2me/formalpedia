-- Prove2me | Definitions.Def_TemperleyLieb_Gram_Models
-- name    : TemperleyLieb_Gram_Models
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:44:28.80956+00:00
-- url     : https://prove2.me/theorems/7f2c5e9c-57f1-4b04-9296-487e975d3d90
-- title:
--   §4–5, pp. 17–19 — integral and fraction-field cell data
-- statement:
--   Write $R=\mathbb Z[x]$ and $F=\operatorname{Frac}(R)$. The integral cellular datum is a cellular basis for $A_n(x)$ over $R$; the field datum is the corresponding basis for $A_n(x)$ over $F$. A paper-specific Jucys–Murphy datum has the operators $T_k$ and contents $r_t(k)$ after mapping their coefficients into $F$:
--
--   $$L_k=T_k,\qquad c_t(k)=r_t(k).$$
--
--   These type aliases and the matching predicate make the seminormal projector from the published cellular-algebra package refer to the paper's actual operators and tableaux.
--
--   **Formalization Note** The field algebra is presented by the same generators and relations over $F$; this is the base change of the integral presentation. The model adds no cellularity or eigenvalue assertion: those are theorem targets.
-- source:
--   Enyang, Representations of Temperley–Lieb Algebras, arXiv:0710.3218v1, p. 17, field F and A_n(x) over F; pp. 15–16, r_t(k) and z_t(k)

import Mathlib
import Definitions.Def_TemperleyLieb_Gram_JM

noncomputable section

namespace TemperleyLieb.Gram

open QAlgorithms.Papers.Independent.Support21.P08

abbrev R := Polynomial ℤ
abbrev F := FractionRing R
def xF : F := algebraMap R F Polynomial.X

abbrev RDatum (n : ℕ) :=
  CellDatum (R := R) (A := TL R Polynomial.X n) (T := Tab n)
abbrev FDatum (n : ℕ) :=
  CellDatum (R := F) (A := TL F xF n) (T := Tab n)

/-- The field-valued content is the image of the integral p. 15 polynomial. -/
def rF {n : ℕ} {f : Fin (n / 2 + 1)} (t : Tab n f) (k : ℕ) : F :=
  algebraMap R F (r t k)

def ztF {n : ℕ} {f : Fin (n / 2 + 1)} (t : Tab n f) (k : ℕ) : F :=
  algebraMap R F (zt t k)

/-- The JM datum uses the displayed `T_k` and their p. 15 contents. -/
def IsPaperJMFamily (n : ℕ) (D : FDatum n) (J : JMFamily D (n + 1)) : Prop :=
  (∀ k : Fin (n + 1), J.L k = JM F xF n k) ∧
  (∀ (f : Fin (n / 2 + 1)) (t : Tab n f) (k : Fin (n + 1)),
    J.content ⟨f, t⟩ k = rF t k)

end TemperleyLieb.Gram


