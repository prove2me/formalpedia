-- Prove2me | Definitions.Def_K230_nd
-- name    : K230_nd
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T21:12:57.581498+00:00
-- url     : https://prove2.me/theorems/fb52c139-87a7-4bb3-9ae8-327a724f06b7
-- title:
--   K230: classical natural deduction
-- statement:
--   Classical first-order natural deduction `Prv` (the relation $A \vdash_C \varphi$) with the sixteen rules of `FullND.v`, including Peirce's law $((\varphi\to\psi)\to\varphi)\to\varphi$ as the classical principle. `TPrv T φ` (written $T \vdash_{TC} \varphi$) means some finite list of axioms drawn from the theory $T$ classically derives $\varphi$.
-- source:
--   https://github.com/elliotglazer/k230-rocq/blob/main/coq/settheory/KPrimeTheory.v

import Definitions.Def_K230_fol
namespace K230
def shiftA (A : List Form) : List Form := A.map (fun φ => subst φ shift)
inductive Prv : List Form → Form → Prop where
  | II {A : List Form} {φ ψ : Form} : Prv (φ :: A) ψ → Prv A (.impl φ ψ)
  | IE {A : List Form} {φ ψ : Form} : Prv A (.impl φ ψ) → Prv A φ → Prv A ψ
  | AllI {A : List Form} {φ : Form} : Prv (shiftA A) φ → Prv A (.all φ)
  | AllE {A : List Form} {t : Nat} {φ : Form} : Prv A (.all φ) → Prv A (subst φ (scons t id))
  | ExI {A : List Form} {t : Nat} {φ : Form} : Prv A (subst φ (scons t id)) → Prv A (.ex φ)
  | ExE {A : List Form} {φ ψ : Form} : Prv A (.ex φ) → Prv (φ :: shiftA A) (subst ψ shift) → Prv A ψ
  | Exp {A : List Form} {φ : Form} : Prv A .falsity → Prv A φ
  | Ctx {A : List Form} {φ : Form} : φ ∈ A → Prv A φ
  | CI {A : List Form} {φ ψ : Form} : Prv A φ → Prv A ψ → Prv A (.conj φ ψ)
  | CE1 {A : List Form} {φ ψ : Form} : Prv A (.conj φ ψ) → Prv A φ
  | CE2 {A : List Form} {φ ψ : Form} : Prv A (.conj φ ψ) → Prv A ψ
  | DI1 {A : List Form} {φ ψ : Form} : Prv A φ → Prv A (.disj φ ψ)
  | DI2 {A : List Form} {φ ψ : Form} : Prv A ψ → Prv A (.disj φ ψ)
  | DE {A : List Form} {φ ψ θ : Form} : Prv A (.disj φ ψ) → Prv (φ :: A) θ → Prv (ψ :: A) θ → Prv A θ
  | Pc {A : List Form} {φ ψ : Form} : Prv A (.impl (.impl (.impl φ ψ) φ) φ)
def TPrv (T : Form → Prop) (φ : Form) : Prop :=
  ∃ A : List Form, (∀ ψ ∈ A, T ψ) ∧ Prv A φ
end K230


