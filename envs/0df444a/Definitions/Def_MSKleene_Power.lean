-- Prove2me | Definitions.Def_MSKleene_Power
-- name    : MSKleene_Power
-- status  : Definition
-- author  : @Cosme
-- created : 2026-09-08T12:27:02.087026+00:00
-- url     : https://prove2.me/theorems/e287ee4f-54be-496c-a9aa-26a0a9a0e58a
-- title:
--   The power $\Sigma$-algebra $A^{\wp}$
-- statement:
--   The **power (subset) $\Sigma$-algebra** $A^{\wp}$ associated with a many-sorted $\Sigma$-algebra $A$ (Proposition 2.32; for single-sorted algebras, Mezei–Wright 1967).
--
--   Its carrier is the sortwise powerset $s \mapsto \mathrm{Set}(A_s)$. For an operation symbol $\sigma$ of rank $(\mathbf{s},s)$ and a tuple of subsets $(L_i)_i$, the interpreted operation returns the image
--   $$\sigma^{A^{\wp}}((L_i)_i) = \{\, \sigma^{A}((x_i)_i) \mid x_i \in L_i \text{ for every } i \,\}.$$
--   The predicate `Args.pmem` expresses that an argument tuple is a componentwise member of a tuple of subsets, and `powerOp` packages the image above. The singleton $S$-sorted map $\{\cdot\}^{\Sigma}_A : A \to A^{\wp}$, $x \mapsto \{x\}$, is also defined.
--
--   This object is where regular expressions are interpreted as languages.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026, https://arxiv.org/abs/1808.08217 (predecessor CVCL20)

/-
The power (subset) `Σ`-algebra `A^℘` associated with a many-sorted `Σ`-algebra
`A` (Proposition 2.32; for single-sorted algebras, Mezei–Wright 1967, Def. 2.2).

Carrier: sortwise powerset `s ↦ Set (A_s)`.
Operation `σ^{A^℘}`: sends a tuple of subsets `(L_i)` to the image
`{ σ^A(x_i) | x_i ∈ L_i for every i }`.

Also: the singleton map `{·} : A → A^℘`, `x ↦ {x}`, as an `S`-sorted map.
-/
import Definitions.Def_MSKleene_Core

namespace MSKleene

universe u

variable {S : Type u} {sig : Signature S}

/-- `Args.pmem xs Ls` holds when the argument tuple `xs` is a componentwise
member of the tuple of subsets `Ls`. -/
def Args.pmem {A : SSet S} :
    {w : List S} → Args A w → Args (fun s => Set (A s)) w → Prop
  | [], _, _ => True
  | _ :: _, (x, xs), (L, Ls) => x ∈ L ∧ Args.pmem xs Ls

/-- The image of a tuple of subsets under an operation of the algebra `A`:
`{ A.op σ xs | xs a componentwise member of Ls }`. -/
def powerOp (A : Algebra sig) {w : List S} {s : S} (σ : sig w s)
    (Ls : Args (fun s => Set (A.carrier s)) w) : Set (A.carrier s) :=
  { y | ∃ xs : Args A.carrier w, Args.pmem xs Ls ∧ y = A.op σ xs }

/-- The power `Σ`-algebra `A^℘` (Proposition 2.32). -/
def powerAlgebra (A : Algebra sig) : Algebra sig where
  carrier := fun s => Set (A.carrier s)
  op := fun σ Ls => powerOp A σ Ls

@[simp] theorem powerAlgebra_carrier (A : Algebra sig) (s : S) :
    (powerAlgebra A).carrier s = Set (A.carrier s) := rfl

@[simp] theorem powerAlgebra_op (A : Algebra sig) {w : List S} {s : S}
    (σ : sig w s) (Ls : Args (fun s => Set (A.carrier s)) w) :
    (powerAlgebra A).op σ Ls = powerOp A σ Ls := rfl

/-- The singleton `S`-sorted map `{·}^Σ_A : A → A^℘`. -/
def singletonMap (A : Algebra sig) : SMap A.carrier (powerAlgebra A).carrier :=
  fun s a => ({a} : Set (A.carrier s))

theorem singletonMap_apply (A : Algebra sig) (s : S) (a : A.carrier s) :
    singletonMap A s a = ({a} : Set (A.carrier s)) := rfl

end MSKleene


