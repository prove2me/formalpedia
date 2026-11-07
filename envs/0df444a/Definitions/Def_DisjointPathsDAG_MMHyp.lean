-- Prove2me | Definitions.Def_DisjointPathsDAG_MMHyp
-- name    : DisjointPathsDAG_MMHyp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:45.8422+00:00
-- url     : https://prove2.me/theorems/75a347c3-2f00-4909-9998-6a7edf222c82
-- title:
--   The matrix-multiplication hypothesis of Theorem 4.1 and Propositions 4.4–4.6
-- statement:
--   The hypothesis "$h\times h$ matrices over $R$ can be multiplied by a division-free straight-line program that is constructible in time linear in its length and uses $O(h^\alpha)$ operations". It is stated about a generator program $\mathrm{gen}$ for the machine with constants $A'$ and $C'$: for every $h\ge1$, on input $h$ it halts on every tape within $C'(\text{size}+1)$ steps and writes a program of size at most $C'h^\alpha$ (constants from a table $\mathrm{cst}$) that multiplies two $h\times h$ matrices over $R$,
--
--   1. as a function on $R$-matrices (the hypothesis of Proposition 4.4, as printed), or
--   2. as an identity of formal polynomials (the strengthening Section 4.5 assumes for Proposition 4.6).
--
--   The **workspace** of the multiplication programs for sizes up to $H$ is the largest space of a program written by $\mathrm{gen}$ on an input $h\le H$.
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Theorem 4.1, p.10; Proposition 4.4, p.16; Section 4.5, p.20

import Mathlib
import Definitions.Def_DisjointPathsDAG_Machine

set_option autoImplicit false

namespace DisjointPathsDAG

/-!
# The matrix-multiplication hypothesis

Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Theorem 4.1, p.10 and Proposition 4.4, p.16:
"h × h matrices over R can be multiplied by a division-free straight-line program that is constructible
in time linear in its length and uses O(hα) operations for some α > 2"; Section 4.5, p.20: "we assume
that the matrix multiplication program of Proposition 4.4 computes the product as an identity of formal
polynomials and is constructible in time linear in its length".

**Formalization Note** The hypothesis is about a generator program `gen` for the machine, with width
constant `A` and constant `C`: on input `h ≥ 1` it writes, in at most `C · (size + 1)` steps, a
program of size at most `C · h^α` that multiplies two `h × h` matrices. `MMSpec` asks for the product as
a function on `R`-matrices, with constants from the table `cst` (the weaker hypothesis, as printed in
Proposition 4.4); `MMSpecFormal` asks for the identity of formal polynomials (Section 4.5). `mmWork`
is the workspace (`SLP.space`) of the multiplication programs written by `gen` for sizes `h ≤ H`.
-/

/-- Matrix multiplication over `R` by machine-generated division-free programs of size `O(h^α)`,
computing the product as a function, constructible in time linear in their length. -/
def MMSpec (R : Type) [CommRing R] (α : ℝ) (cst : ℕ → R) (gen : Program) (A : ℕ) (C : ℝ) : Prop :=
  ∀ h : ℕ, 1 ≤ h → GeneratesSLP gen A [h] C fun P =>
    ComputesMatMulFun R cst h h h P ∧ (P.size : ℝ) ≤ C * (h : ℝ) ^ α

/-- As `MMSpec`, with the product computed as an identity of formal polynomials. -/
def MMSpecFormal (R : Type) [CommRing R] (α : ℝ) (cst : ℕ → R) (gen : Program) (A : ℕ) (C : ℝ) :
    Prop :=
  ∀ h : ℕ, 1 ≤ h → GeneratesSLP gen A [h] C fun P =>
    ComputesMatMul R cst h h h P ∧ (P.size : ℝ) ≤ C * (h : ℝ) ^ α

/-- The workspace of the multiplication programs: the largest `SLP.space` of a program written by a
halting run of `gen` on an input `h ≤ H` (width `wordWidth A`, any tape). -/
noncomputable def mmWork (gen : Program) (A : ℕ) (H : ℕ) : ℕ∞ :=
  ⨆ (h : ℕ) (_ : h ≤ H) (ω : Tape (ZMod 2)) (t : ℕ)
    (_ : HaltsAt (wordWidth A (Input.size (⟨[h], [], []⟩ : Input (ZMod 2)))) (ZMod 2) gen
      ⟨[h], [], []⟩ ω t),
    (((SLP.decode (outWords (⟨[h], [], []⟩ : Input (ZMod 2))
      (stateAt (wordWidth A (Input.size (⟨[h], [], []⟩ : Input (ZMod 2)))) (ZMod 2) gen
        ⟨[h], [], []⟩ ω t))).space : ℕ) : ℕ∞)

end DisjointPathsDAG


