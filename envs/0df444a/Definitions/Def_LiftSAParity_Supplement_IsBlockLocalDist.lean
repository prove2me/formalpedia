-- Prove2me | Definitions.Def_LiftSAParity_Supplement_IsBlockLocalDist
-- name    : LiftSAParity_Supplement_IsBlockLocalDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:12:21.9752+00:00
-- url     : https://prove2.me/theorems/4ea72b94-0f16-4ccf-a4c7-9359485a05ef
-- title:
--   Block $d$-local distribution for a blockwise CNF formula
-- statement:
--   Let $\varphi$ be a CNF formula over the variables $x_{ij}$, $(i,j)\in[n]\times[\ell]$, grouped into $n$ **blocks** $\{i\}\times[\ell]$ of $\ell$ variables each. A **blockwise partial assignment** $\tau$ with support $\mathrm{supp}(\tau)=I\subseteq[n]$ assigns every variable of every block in $I$ and no other variable; it **falsifies** a clause $C$ if every variable of $C$ lies in $I\times[\ell]$ and every literal of $C$ is false under $\tau$.
--
--   A **block $d$-local distribution** for $\varphi$ is a family $\mathcal D=\{\mathcal D_I\}$, one probability distribution on $\{0,1\}^{I\times[\ell]}$ for every set of blocks $I\subseteq[n]$ with $|I|\le d$, such that
--
--   1. no assignment in the support of $\mathcal D_I$ falsifies a clause of $\varphi$ whose variables all lie in $I\times[\ell]$;
--   2. the distributions are consistent: for all $I,K$ with $|I|,|K|\le d$, the marginals of $\mathcal D_I$ and $\mathcal D_K$ on the blocks $I\cap K$ are equal.
--
--   This is the $d$-local distribution of §1.1 "with variables replaced by blocks of variables"; it is the object from which Sections 5 and 6 build pseudo-measures and size lower bounds.
--
--   **Formalization Note** $|I|$ counts blocks, not variables, so this differs from the variable-level `LiftSAParity.IsLocalDist`. A blockwise assignment on $I$ is a function $I\to(\mathrm{Fin}\,\ell\to\mathbb F_2)$; `Agrees x τ` says a total assignment extends $\tau$, and `Compat τ σ` says two blockwise assignments agree on their common blocks. The values $\mathcal D_I$ for $|I|>d$ are unconstrained.
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §1.1, p.4 (d-local distribution, "with variables replaced by blocks"); §2, p.7 (blockwise partial assignments); §5.2, p.17

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_LiftSAParity_IsAffineSpace

namespace LiftSAParity

namespace Supplement

open Classical

/-- A **blockwise partial assignment** with support `I ⊆ [n]` (de Rezende–Engström–Shekhovtsov,
*Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size*, manuscript (sha256
cab5a032…), §2, p.7 and §5.2, p.17): it assigns all `ℓ` variables `x_{i1}, …, x_{iℓ}` of every
block `i ∈ I = supp(σ)` and no variable outside these blocks.

**Formalization Note** Values are in `𝔽₂ = ZMod 2` (`1` = true), the convention of the published
affine-space definitions. -/
abbrev BlockAssign (n ℓ : ℕ) (I : Finset (Fin n)) := ↥I → Fin ℓ → ZMod 2

/-- A total assignment `x ∈ 𝔽₂^{[n]×[ℓ]}` **extends** the blockwise partial assignment `τ`
(`x ⊇ τ`, §2, p.7): they agree on every variable of every block of `supp(τ)`. -/
def Agrees {n ℓ : ℕ} {I : Finset (Fin n)} (x : Fin n × Fin ℓ → ZMod 2) (τ : BlockAssign n ℓ I) :
    Prop :=
  ∀ (i : ↥I) (j : Fin ℓ), x (i.1, j) = τ i j

/-- Two blockwise partial assignments `τ` (support `I`) and `σ` (support `S`) **agree**: they
assign the same values on every block of `I ∩ S`. When `S ⊆ I` this is "`τ` agrees with `σ`"
(§5.2, p.17). -/
def Compat {n ℓ : ℕ} {I S : Finset (Fin n)} (τ : BlockAssign n ℓ I) (σ : BlockAssign n ℓ S) :
    Prop :=
  ∀ (i : Fin n) (hi : i ∈ I) (hs : i ∈ S) (j : Fin ℓ), τ ⟨i, hi⟩ j = σ ⟨i, hs⟩ j

/-- The blockwise partial assignment `τ` (support `I`) **falsifies the clause** `C`: every
variable of `C` lies in a block of `I` (i.e. in `I × [ℓ]`) and every literal of `C` is false under
`τ`. The literal `(v, b)` is true iff `x_v = b` (with `true = 1`). The empty clause is falsified
by every `τ`. -/
def FalsifiesOn {n ℓ : ℕ} {I : Finset (Fin n)} (τ : BlockAssign n ℓ I)
    (C : Clause (Fin n × Fin ℓ)) : Prop :=
  ∀ l ∈ C, ∃ h : l.1.1 ∈ I, τ ⟨l.1.1, h⟩ l.1.2 ≠ ofBool l.2

/-- **Block d-local distribution** (§1.1, p.4: "Later we use the same definition with variables
replaced by blocks of variables"; §5.2, p.17; §6.1, p.20). For a CNF `φ` over the variables
`[n] × [ℓ]`, a family `D = {D_I}`, one probability distribution on `{0,1}^{I×[ℓ]}` for every set of
blocks `I ⊆ [n]` with `|I| ≤ d`, such that
(1) no assignment in the support of `D_I` falsifies a clause of `φ` whose variables all lie in
`I × [ℓ]`; and
(2) the distributions are consistent: for all `I, K` with `|I|, |K| ≤ d` the marginals of `D_I`
and `D_K` on the blocks `I ∩ K` are equal.

`D I τ` is the probability of `τ : {0,1}^{I×[ℓ]}` under `D_I`.

**Formalization Note** `|I|` counts **blocks**, not variables (this is not the published
variable-level `LiftSAParity.IsLocalDist`). The values `D I` for `|I| > d` are unconstrained. The
marginal of `D_I` at `ρ ∈ {0,1}^{(I∩K)×[ℓ]}` is the total mass of the `τ` agreeing with `ρ`. -/
def IsBlockLocalDist {n ℓ : ℕ} (φ : CNF (Fin n × Fin ℓ)) (d : ℕ)
    (D : (I : Finset (Fin n)) → BlockAssign n ℓ I → ℝ) : Prop :=
  (∀ I : Finset (Fin n), I.card ≤ d → (∀ τ, 0 ≤ D I τ) ∧ ∑ τ, D I τ = 1) ∧
  (∀ I : Finset (Fin n), I.card ≤ d → ∀ τ : BlockAssign n ℓ I, 0 < D I τ →
      ∀ C ∈ φ, ¬ FalsifiesOn τ C) ∧
  (∀ I K : Finset (Fin n), I.card ≤ d → K.card ≤ d → ∀ ρ : BlockAssign n ℓ (I ∩ K),
      ∑ τ ∈ Finset.univ.filter (fun τ : BlockAssign n ℓ I => Compat τ ρ), D I τ =
        ∑ τ ∈ Finset.univ.filter (fun τ : BlockAssign n ℓ K => Compat τ ρ), D K τ)

end Supplement

end LiftSAParity


