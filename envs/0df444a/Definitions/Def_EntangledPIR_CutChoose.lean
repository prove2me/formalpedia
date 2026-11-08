-- Prove2me | Definitions.Def_EntangledPIR_CutChoose
-- name    : EntangledPIR_CutChoose
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:40.473922+00:00
-- url     : https://prove2.me/theorems/ce60ea4d-567b-4856-abec-36c862849cda
-- title:
--   The cut-and-choose operators $P^t_S$, $E^t_s$, $\Pi_t$, $Q_C$, $Q_s$ and the maps $A$, $R_x$, $R^a_x$
-- statement:
--   The setting of §3. Given projectors $\Pi_{i,j}$ on the copies with
--
--   $$\Pi_{i,j}|J\rangle\langle J|_{\mathsf P'_{i,j}}\Pi_{i,j}=2^{-d}\Pi_{i,j}\quad(3.1),$$
--
--   positions $t\in[\ell]^k$ and sets $S\subseteq[k]$, $C\subseteq[k]\times[\ell]$, the module defines
--
--   $$P^t_S=\prod_{i\in S}(1-\Pi_{i,t_i})\prod_{i\notin S}\Pi_{i,t_i},\quad E^t_s=\sum_{|S|=s}P^t_S,\quad \Pi_t=\prod_i\prod_{j\ne t_i}\Pi_{i,j},\quad Q_C=\prod_{(i,j)\in C}(1-\Pi_{i,j})\prod_{(i,j)\notin C}\Pi_{i,j},$$
--
--   with $Q_s$ the sum of $Q_C$ over the sets $C$ with one copy of each of exactly $s$ shares, $p_s=\mathrm{Tr}(Q_s\rho)$, and the maps
--
--   $$A(\Xi)=\sum_t|t\rangle\langle t|_{\mathsf T}\otimes\ell^{-k}\Pi_t\Xi\Pi_t,$$
--
--   $$R_x(\Xi)=\sum_{t}\sum_{K}|t\rangle\langle t|_{\mathsf T}\otimes\mathbb E_{y\sim\mu_x}\mathrm{Tr}_{\mathsf B}\bigl[|K\oplus y\rangle\langle K\oplus y|_t\langle t|\Xi|t\rangle\bigr]\otimes|K\rangle\langle K|_{\mathsf K}.$$
--
--   $R^a_x$ of (5.5) adds $a_t$ to $K\oplus y$. A sharing has privacy threshold $\lambda$ if, for every set of at most $\lambda$ indices, the joint distribution of those shares is the same for all secrets.
--
--   **Formalization Note** `RmapShift` covers both $R_x$ and $R^a_x$. `Qs` uses a classical filter, since the condition on $C$ is a proposition.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), §3, (3.1), (3.3)–(3.5), pp.12–16; (5.5), p.28

import Definitions.Def_EntangledPIR_CopyB
import Definitions.Def_WildeQIT_partialTrace

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), §3,
pp.12–16: the operators of the cut-and-choose procedure.
-/

open Matrix
open scoped Kronecker

namespace EntangledPIR

section
variable {k ℓ d : ℕ} {E : Fin k × Fin ℓ → Type}
  [∀ c, Fintype (E c)] [∀ c, DecidableEq (E c)]

/-- The positions `t ∈ [ℓ]^k` of the untested copies, p.12. -/
abbrev Positions (k ℓ : ℕ) : Type := Fin k → Fin ℓ

/-- The share strings `y` or addresses `K ∈ ({0,1}^d)^k`, p.12. -/
abbrev ShareVec (k d : ℕ) : Type := Fin k → Bits d

/-- `|J⟩⟨J|_{P′_{i,j}}` on copy `c`. -/
def addrProj (c : Fin k × Fin ℓ) (J : Bits d) : Matrix (CopyB d E c) (CopyB d E c) ℂ :=
  basisProj J ⊗ₖ (1 : Matrix (E c) (E c) ℂ)

/-- **The hypotheses on the tests**, p.12: each `Π_{i,j}` is a projector on `B_{i,j}`, and (3.1),
`Π_{i,j} |J⟩⟨J|_{P′_{i,j}} Π_{i,j} = 2^{-d} Π_{i,j}`. -/
structure IsTestFamily (Pi : ∀ c, Matrix (CopyB d E c) (CopyB d E c) ℂ) : Prop where
  hermitian : ∀ c, (Pi c).IsHermitian
  idempotent : ∀ c, Pi c * Pi c = Pi c
  eq_3_1 : ∀ c (J : Bits d), Pi c * addrProj c J * Pi c = ((2 : ℂ) ^ d)⁻¹ • Pi c

/-- `P^t_S = ∏_{i∈S} (1 − Π_{i,t_i}) ∏_{i∉S} Π_{i,t_i}` of (3.3), p.14. -/
def PtS (Pi : ∀ c, Matrix (CopyB d E c) (CopyB d E c) ℂ) (t : Positions k ℓ) (S : Finset (Fin k)) :
    Matrix (AllB d E) (AllB d E) ℂ :=
  ICSCompute.piTensor fun c =>
    if c.2 = t c.1 then (if c.1 ∈ S then 1 - Pi c else Pi c) else 1

/-- `E^t_s = ∑_{S ⊆ [k], |S| = s} P^t_S` of (3.3), p.14. -/
def Ets (Pi : ∀ c, Matrix (CopyB d E c) (CopyB d E c) ℂ) (t : Positions k ℓ) (s : ℕ) :
    Matrix (AllB d E) (AllB d E) ℂ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun S => S.card = s), PtS Pi t S

/-- `|J⟩⟨J|_t = ⊗_i |J_i⟩⟨J_i|_{P′_{i,t_i}}`, p.15. -/
def JProj (t : Positions k ℓ) (J : ShareVec k d) : Matrix (AllB d E) (AllB d E) ℂ :=
  ICSCompute.piTensor fun c => if c.2 = t c.1 then addrProj c (J c.1) else 1

/-- `Π_t = ∏_i ∏_{j≠t_i} Π_{i,j}`, p.15. -/
def PiT (Pi : ∀ c, Matrix (CopyB d E c) (CopyB d E c) ℂ) (t : Positions k ℓ) :
    Matrix (AllB d E) (AllB d E) ℂ :=
  ICSCompute.piTensor fun c => if c.2 ≠ t c.1 then Pi c else 1

/-- `Q_C = ∏_{(i,j)∈C} (1 − Π_{i,j}) ∏_{(i,j)∉C} Π_{i,j}`, p.15. -/
def QC (Pi : ∀ c, Matrix (CopyB d E c) (CopyB d E c) ℂ) (C : Finset (Fin k × Fin ℓ)) :
    Matrix (AllB d E) (AllB d E) ℂ :=
  ICSCompute.piTensor fun c => if c ∈ C then 1 - Pi c else Pi c

/-- `C` contains one copy of each of exactly `s` shares and no other copy, p.16. -/
def OneCopyPerShare (C : Finset (Fin k × Fin ℓ)) (s : ℕ) : Prop :=
  C.card = s ∧ ∀ c ∈ C, ∀ c' ∈ C, c.1 = c'.1 → c = c'

open Classical in
/-- `Q_s`, the sum of `Q_C` over those `C`, p.16. -/
noncomputable def Qs (Pi : ∀ c, Matrix (CopyB d E c) (CopyB d E c) ℂ) (s : ℕ) :
    Matrix (AllB d E) (AllB d E) ℂ :=
  ∑ C ∈ (Finset.univ : Finset (Finset (Fin k × Fin ℓ))).filter (fun C => OneCopyPerShare C s),
    QC Pi C

section
variable {R : Type} [Fintype R] [DecidableEq R]

/-- `O` acting on `B` inside `RB`: `1_R ⊗ O`. -/
def onB (O : Matrix (AllB d E) (AllB d E) ℂ) : Matrix (R × AllB d E) (R × AllB d E) ℂ :=
  (1 : Matrix R R ℂ) ⊗ₖ O

/-- `p_s = Tr(Q_s ρ)`, p.16: the probability that the tests of all `kℓ` copies, applied to `ρ`, fail
at exactly one copy of each of exactly `s` shares and pass at all others. -/
noncomputable def probS (Pi : ∀ c, Matrix (CopyB d E c) (CopyB d E c) ℂ)
    (ρ : Matrix (R × AllB d E) (R × AllB d E) ℂ) (s : ℕ) : ℝ :=
  (Matrix.trace (onB (Qs Pi s) * ρ)).re

/-- The map `A` of (3.5), p.16: `A(Ξ) = ∑_t |t⟩⟨t|_T ⊗ ℓ^{-k} Π_t Ξ Π_t`, for `Ξ` on `RB`. -/
noncomputable def Amap (Pi : ∀ c, Matrix (CopyB d E c) (CopyB d E c) ℂ)
    (Ξ : Matrix (R × AllB d E) (R × AllB d E) ℂ) :
    Matrix (Positions k ℓ × (R × AllB d E)) (Positions k ℓ × (R × AllB d E)) ℂ :=
  ∑ t : Positions k ℓ,
    classicalBlock t (((ℓ : ℂ) ^ k)⁻¹ • (onB (PiT Pi t) * Ξ * onB (PiT Pi t)))

/-- The maps `R_x` of (3.4), p.15, and `R^a_x` of (5.5), p.28, in one definition, with `shift t`
the string added to `K` for positions `t`: for `Ξ` on `T R B` the result is the operator on `T R K`
`∑_t ∑_K |t⟩⟨t|_T ⊗ E_{y∼µ} Tr_B[|K ⊕ shift t ⊕ y⟩⟨K ⊕ shift t ⊕ y|_t ⟨t|Ξ|t⟩] ⊗ |K⟩⟨K|_K`.
The distribution `µ` of the shares is given by its probabilities. -/
noncomputable def RmapShift (shift : Positions k ℓ → ShareVec k d) (mu : ShareVec k d → ℝ)
    (Ξ : Matrix (Positions k ℓ × (R × AllB d E)) (Positions k ℓ × (R × AllB d E)) ℂ) :
    Matrix (Positions k ℓ × (R × ShareVec k d)) (Positions k ℓ × (R × ShareVec k d)) ℂ :=
  Matrix.of fun p q =>
    if p.1 = q.1 ∧ p.2.2 = q.2.2 then
      ∑ y : ShareVec k d, (mu y : ℂ) *
        WildeQIT.partialTraceRight
          (onB (R := R) (JProj (E := E) p.1
              (fun i => bxor (bxor (p.2.2 i) (shift p.1 i)) (y i))) *
            Matrix.of fun (u v : R × AllB d E) => Ξ (p.1, u) (p.1, v))
          p.2.1 q.2.1
    else 0

/-- `R_x` of (3.4), p.15: `RmapShift` with no shift. -/
noncomputable def Rmap (mu : ShareVec k d → ℝ)
    (Ξ : Matrix (Positions k ℓ × (R × AllB d E)) (Positions k ℓ × (R × AllB d E)) ℂ) :
    Matrix (Positions k ℓ × (R × ShareVec k d)) (Positions k ℓ × (R × ShareVec k d)) ℂ :=
  RmapShift (fun _ _ => bzero d) mu Ξ

end

/-- **Privacy threshold**, p.12. For every set of at most `lam` indices `i`, the joint distribution
of the shares `y_i` with these indices is the same for all secrets: for all `x, x′` and every value
`z` of these shares, the two probabilities of `y|_S = z|_S` agree. -/
def HasPrivacyThreshold {X : Type} (mu : X → ShareVec k d → ℝ) (lam : ℕ) : Prop :=
  ∀ S : Finset (Fin k), S.card ≤ lam → ∀ (x x' : X) (z : ShareVec k d),
    ∑ y ∈ Finset.univ.filter (fun y : ShareVec k d => ∀ i ∈ S, y i = z i), mu x y =
      ∑ y ∈ Finset.univ.filter (fun y : ShareVec k d => ∀ i ∈ S, y i = z i), mu x' y

/-- A family of distributions of shares, one for each secret, p.12. -/
def IsShareDistribution {X : Type} (mu : X → ShareVec k d → ℝ) : Prop :=
  ∀ x, (∀ y, 0 ≤ mu x y) ∧ ∑ y, mu x y = 1

end

end EntangledPIR


