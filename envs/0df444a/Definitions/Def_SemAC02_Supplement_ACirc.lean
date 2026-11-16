-- Prove2me | Definitions.Def_SemAC02_Supplement_ACirc
-- name    : SemAC02_Supplement_ACirc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:39:53.285125+00:00
-- url     : https://prove2.me/theorems/c3e8dbf6-6664-4373-90fe-a36db72fa326
-- title:
--   Layered algebraic circuits: ΣΠΣ, ΣΠΣΠ and ΣΠΣΠ[w] lines
-- statement:
--   An **algebraic circuit** over a field $\mathbb F$ with Boolean variables $x_i$ ($i\in\sigma$) has leaves labelled by variables or field elements, **plus gates** $\Sigma$ computing a linear combination of their inputs with weights on the incoming edges, and **product gates** $\Pi$ computing the product of their inputs; fan-in is unbounded. The class of a circuit in $B_\sigma(\mathbb F)=\mathbb F[x]/\langle x_i^2-x_i\rangle$ is identified with the function it computes on $\{0,1\}^\sigma$.
--
--   Layered circuits alternate $\Sigma$ and $\Pi$ layers, numbered from the output:
--
--   1. a **ΣΠΣ circuit** is a top plus gate over product gates over bottom plus gates fed by leaves; every bottom gate computes an affine form $a_0+\sum_i a_ix_i$, and the polynomials computed by the product gates are the **product terms**;
--   2. a **ΣΠΣΠ circuit** is a top plus gate over product gates (the **top product terms**) over plus gates (the **bottom polynomials**) over bottom product gates fed by leaves; in a **ΣΠΣΠ[w] circuit** every bottom product gate has fan-in at most $w$.
--
--   The size $|C|$ of a circuit is its number of vertices, i.e. the number of its distinct rooted subcircuits.
--
--   These are the proof lines of semantic ΣΠΣ-PC and ΣΠΣΠ-PC.
--
--   **Formalization Note** A circuit is a term of the inductive type `ACirc F σ`; the DAG with maximal sharing is obtained by identifying equal subterms (`subterms`). Edge weights are stored with the children of a plus gate and are not vertices. Empty gates are allowed (an empty sum is $0$, an empty product $1$). `cval` is the value on the cube, `mlz` the multilinearisation over any field, `topTerms` the children of the top gate, `bottomPolys` the children of the top product gates.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §2, p.14 (PDF p.16); §7.3.1, p.54 (PDF p.56)

import Mathlib
import Definitions.Def_AC02Frege_ML

namespace SemAC02.Supplement

open MvPolynomial

/-- **Algebraic circuits** over a field `F` with Boolean variables `σ` (Alekseev–Gryaznov–Itsykson–
Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027
submission), §2, p.14): leaves are variables (`var`) or field elements (`const`); a plus gate
(`sum`) computes the linear combination of its inputs with the weights on its incoming edges; a
product gate (`prod`) computes the product of its inputs. Fan-in is unbounded.

**Formalization Note** A circuit is a term; the paper's DAG with maximal sharing is recovered by
identifying equal subterms (`subterms`), so that "the number of vertices" and "the number of
distinct rooted subcircuits" are the number of distinct subterms. An edge weight is stored with the
child in the list of a `sum` gate; the paper's size counts vertices, not weights (field elements
and edge weights have unit cost). Empty gates are allowed: an empty sum is `0`, an empty product
is `1`. -/
inductive ACirc (F : Type) (σ : Type) where
  | var : σ → ACirc F σ
  | const : F → ACirc F σ
  | sum : List (F × ACirc F σ) → ACirc F σ
  | prod : List (ACirc F σ) → ACirc F σ

namespace ACirc

variable {F σ : Type}

/-- The polynomial computed by a circuit, in `F[x]` (before the Boolean quotient). -/
noncomputable def toPoly [CommRing F] : ACirc F σ → MvPolynomial σ F
  | var i => X i
  | const c => C c
  | sum ps => (ps.attach.map (fun p => C p.1.1 * toPoly p.1.2)).sum
  | prod cs => (cs.attach.map (fun c => toPoly c.1)).prod
termination_by c => c
decreasing_by
  all_goals first
    | (obtain ⟨⟨a, b⟩, hp⟩ := p; have h := List.sizeOf_lt_of_mem hp; simp at h ⊢; omega)
    | (obtain ⟨c, hc⟩ := c; have h := List.sizeOf_lt_of_mem hc; simp at h ⊢; omega)

/-- The set of distinct rooted subcircuits of a circuit (the circuit and, recursively, the
subcircuits of its children). -/
noncomputable def subterms : ACirc F σ → Finset (ACirc F σ)
  | var i => {var i}
  | const c => {const c}
  | sum ps => open Classical in
      insert (sum ps) ((ps.attach.map (fun p => subterms p.1.2)).foldr (· ∪ ·) ∅)
  | prod cs => open Classical in
      insert (prod cs) ((cs.attach.map (fun c => subterms c.1)).foldr (· ∪ ·) ∅)
termination_by c => c
decreasing_by
  all_goals first
    | (obtain ⟨⟨a, b⟩, hp⟩ := p; have h := List.sizeOf_lt_of_mem hp; simp at h ⊢; omega)
    | (obtain ⟨c, hc⟩ := c; have h := List.sizeOf_lt_of_mem hc; simp at h ⊢; omega)

/-- The circuit is a leaf (a variable or a field element). -/
def IsLeaf : ACirc F σ → Prop
  | var _ => True
  | const _ => True
  | _ => False

/-- The circuit is a plus gate all of whose children satisfy `P`. -/
def IsSumOf (P : ACirc F σ → Prop) : ACirc F σ → Prop
  | sum ps => ∀ p ∈ ps, P p.2
  | _ => False

/-- The circuit is a product gate all of whose children satisfy `P`. -/
def IsProdOf (P : ACirc F σ → Prop) : ACirc F σ → Prop
  | prod cs => ∀ c ∈ cs, P c
  | _ => False

/-- A bottom product gate of fan-in at most `w` (`w = ⊤`: unbounded): a product gate whose
children are leaves. -/
def IsMonGate (w : ℕ∞) : ACirc F σ → Prop
  | prod cs => ((cs.length : ℕ) : ℕ∞) ≤ w ∧ ∀ c ∈ cs, IsLeaf c
  | _ => False

/-- A **ΣΠΣ circuit** (§2, p.14): a top plus gate whose children are product gates whose children
are bottom plus gates fed by leaves (each bottom gate computes an affine form `a₀ + ∑ aᵢxᵢ`). -/
def IsSPS (c : ACirc F σ) : Prop :=
  IsSumOf (IsProdOf (IsSumOf IsLeaf)) c

/-- A **ΣΠΣΠ[w] circuit** (§2, p.14): a top plus gate, second-layer product gates, third-layer plus
gates, and bottom product gates of fan-in at most `w` fed by leaves. `IsSPSP ⊤` is the class of
all (layered) ΣΠΣΠ circuits. -/
def IsSPSP (w : ℕ∞) (c : ACirc F σ) : Prop :=
  IsSumOf (IsProdOf (IsSumOf (IsMonGate w))) c

/-- The children of the top plus gate: for a ΣΠΣ or ΣΠΣΠ circuit these are its (top) product
terms (§2, p.14). -/
def topTerms : ACirc F σ → List (ACirc F σ)
  | sum ps => ps.map Prod.snd
  | _ => []

/-- The bottom polynomials of a ΣΠΣΠ circuit (§7.3.1, p.54): the children of its top product
gates. -/
def bottomPolys : ACirc F σ → List (ACirc F σ)
  | sum ps => ps.flatMap (fun p => match p.2 with
      | prod cs => cs
      | _ => [])
  | _ => []

end ACirc

/-- The `F`-valued point of the cube corresponding to a Boolean assignment (`true ↦ 1`). -/
def boolPt {F σ : Type} [Zero F] [One F] (x : σ → Bool) : σ → F :=
  fun i => if x i then 1 else 0

/-- The value at a Boolean point of a polynomial: `B_σ(F) = F[x]/⟨x_i² − x_i⟩` is identified with
the functions `{0,1}^σ → F` (p.15), and `polyFn p` is the class of `p`. -/
noncomputable def polyFn {F σ : Type} [CommRing F] (p : MvPolynomial σ F) : (σ → Bool) → F :=
  fun x => eval (boolPt x) p

/-- The value of a circuit at a Boolean point, i.e. its class in `B_σ(F)` (p.15: "a circuit in a
proof line represents its residue class"). -/
noncomputable def cval {F σ : Type} [CommRing F] (c : ACirc F σ) : (σ → Bool) → F :=
  polyFn c.toPoly

/-- The multilinearisation of a polynomial over any field: every positive power of a variable is
replaced by the variable, and coefficients of monomials with the same image are added. Its result
is the multilinear representative of the class of the polynomial in `B_σ(F)`. -/
noncomputable def mlz {F σ : Type} [CommRing F] (p : MvPolynomial σ F) : MvPolynomial σ F :=
  ∑ s ∈ p.support, monomial (AC02Frege.sqfree s) (coeff s p)

end SemAC02.Supplement


