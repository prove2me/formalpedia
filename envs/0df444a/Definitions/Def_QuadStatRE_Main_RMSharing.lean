-- Prove2me | Definitions.Def_QuadStatRE_Main_RMSharing
-- name    : QuadStatRE_Main_RMSharing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:45:44.722658+00:00
-- url     : https://prove2.me/theorems/d96d6783-afb3-42ac-a43c-0244a56076ed
-- title:
--   RM(1,4) sharing, Construction 3 (the RM amplification step) and the induced leakage $\mathcal A(W)$
-- statement:
--   Let $I=\mathbb F_2^4\setminus\{0\}$, $|I|=15$ (§4.1, p. 21). To share a bit $a$, choose a uniformly random affine polynomial $p_a(u)=a+\alpha\cdot u$ ($\alpha\in\mathbb F_2^4$) and output $(p_a(u))_{u\in I}$; the three bits of $s\in G$ are shared in parallel by a uniform $A\in\mathbb F_2^{3\times4}$ (no rank restriction):
--   $$s_u=s+Au,\qquad u\in I. \tag{4.1}$$
--
--   **Construction 3** (p. 22). Given an encoding $E$ of $f(x,y,z,w)=xyz+w$, on input $(s,w)$: sample $A$ and compute the fifteen shares $s_u$; independently sample a uniform $(w_u)_{u\in I}$ with $\bigoplus_u w_u=w$; independently run $\mathrm{Enc}_E$ on each child input $(s_u,w_u)$ and output the concatenation of the fifteen child transcripts. The decoder outputs $\bot$ if some child decoder does, and otherwise the XOR of the fifteen decoded values (§4.4, p. 23). The amplified encoder uses the 12 bits of $A$, 14 bits for the sharing of $w$ and the fifteen child tapes, and its description is obtained from $E$'s by affine substitution.
--
--   **Induced leakage** (p. 22). For a leakage family $W$ and a parent secret $s$, $\mathcal A_s(W)$ samples a sharing of $s$ by (4.1), then independently $T_u\leftarrow W_{s_u}$ for every $u$, and outputs $(T_u)_{u\in I}$ ($A$ and the shares are not output):
--   $$\mathcal A_s(W)(T)=2^{-12}\sum_{A\in\mathbb F_2^{3\times4}}\prod_{u\in I}W_{s+Au}(T_u).$$
--   The product reference $R^{\otimes15}$ on $\Omega^I$ is $T\mapsto\prod_u R(T_u)$.
--
--   The RM step is the privacy-amplification procedure that the paper iterates; $\mathcal A$ is the map on leakage families that the $\chi^2$ analysis tracks.
--
--   **Formalization Note.** $I$ is indexed by $k\in\{0,\dots,14\}$: position $k$ is the vector whose coordinate $j$ is bit $j$ of $k+1$, which lists every nonzero vector once. The additive sharing of $w$ uses $w_k=\omega_k$ for $k<14$ and $w_{14}=w+\sum_{k<14}\omega_k$ with $\omega$ uniform, which makes $(w_u)$ uniform subject to $\bigoplus_u w_u=w$. The parent tape is $A$ (positions $0$–$11$, entry $(i,j)$ at $4i+j$), $\omega$ (positions $12$–$25$), then the child tapes in order.
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), pp. 21–23, §4.1 (4.1), Construction 3, Definition (Induced leakage), §4.4

import Mathlib
import Definitions.Def_QuadraticRE_Desc
import Definitions.Def_QuadStatRE_Main_BasicEncoding

namespace QuadStatRE.Main

open QuadraticRE

/-- The fifteen share positions `I = F₂⁴ ∖ {0}` (Applebaum, *Quadratic Statistical Randomized Encoding
for All Functions*, STOC 2027 submission, §4.1, p. 21) are indexed by `k : Fin 15`: position `k` is the
nonzero vector whose coordinate `j` is bit `j` of the binary expansion of `k + 1`. This lists each
nonzero vector of `F₂⁴` exactly once. -/
def uvec (k : Fin 15) : Fin 4 → F2 :=
  fun j => if Nat.testBit (k.val + 1) j.val then 1 else 0

/-- The RM(1,4) share at position `u` of a bit `a` (§4.1, p. 21): an affine polynomial
`p_a(u) = a + α · u` with `p_a(0) = a`, given by its linear part `α ∈ F₂⁴`. -/
def rmShare (a : F2) (α : Fin 4 → F2) (k : Fin 15) : F2 := a + α ⬝ᵥ uvec k

/-- The sharing (4.1) of a triple `s ∈ G`: `s_u = s + A u`, `A ∈ F₂^{3×4}`. -/
def share (s : G) (A : Matrix (Fin 3) (Fin 4) F2) (k : Fin 15) : G := s + A.mulVec (uvec k)

/-- The induced leakage `A_s(W)` under an RM step (Definition on p. 22): sample a uniform
`A ∈ F₂^{3×4}` (no rank restriction), independently `T_u ← W_{s_u}` for every position, output
`(T_u)_{u ∈ I}`; `A` and the shares are not output. As a distribution on `I → Ω`:
`A_s(W)(T) = 2^{-12} ∑_A ∏_u W_{s + A u}(T_u)`. -/
noncomputable def amp {Ω : Type} (W : G → Ω → ℝ) : G → (Fin 15 → Ω) → ℝ :=
  fun s T => ∑ A : Matrix (Fin 3) (Fin 4) F2, (1 / 2 ^ 12 : ℝ) * ∏ k : Fin 15, W (share s A k) (T k)

/-- The product reference `R^{⊗15}` on `I → Ω`: independent coordinates, each distributed as `R`
(§6.1, p. 28). -/
noncomputable def prodRef {Ω : Type} (R : Ω → ℝ) : (Fin 15 → Ω) → ℝ :=
  fun T => ∏ k : Fin 15, R (T k)

section Amplify

variable (ρ : ℕ)

/-- Polynomials over the parent variables, as lists of monomials. -/
abbrev Poly : Type := List (List (Fin 4 ⊕ Fin (12 + (14 + 15 * ρ))))

/-- Parent tape variable for the entry `A_{ij}` of the sharing matrix (12 bits). -/
def aVar (i : Fin 3) (j : Fin 4) : Fin 4 ⊕ Fin (12 + (14 + 15 * ρ)) :=
  .inr (Fin.castAdd (14 + 15 * ρ) (finProdFinEquiv (i, j)))

/-- Parent tape variable `ω_k`, `k < 14`, of the additive sharing of `w` (14 bits). -/
def omVar (k : Fin 14) : Fin 4 ⊕ Fin (12 + (14 + 15 * ρ)) :=
  .inr (Fin.natAdd 12 (Fin.castAdd (15 * ρ) k))

/-- Parent tape variable for tape bit `i` of child `k` (`15 ρ` bits). -/
def childVar (k : Fin 15) (i : Fin ρ) : Fin 4 ⊕ Fin (12 + (14 + 15 * ρ)) :=
  .inr (Fin.natAdd 12 (Fin.natAdd 14 (finProdFinEquiv (k, i))))

/-- The child input `(s_u, w_u)` of child `k`, coordinate `j`, as an affine polynomial in the parent
variables: `(s_u)_j = s_j + ∑_l A_{jl} u_l` for `j < 3`; `w_u = ω_k` for `k < 14` and
`w_u = w + ∑_{k' < 14} ω_{k'}` for the last position, so that `⊕_u w_u = w` with the `w_u` uniform
subject to it (Construction 3 (ii), p. 22). -/
def childInput (k : Fin 15) (j : Fin 4) : Poly ρ :=
  if hj : j.val < 3 then
    [Sum.inl j] :: ((List.finRange 4).filter (fun l => uvec k l = 1)).map
      (fun l => [aVar ρ ⟨j.val, hj⟩ l])
  else if hk : k.val < 14 then [[omVar ρ ⟨k.val, hk⟩]]
  else [Sum.inl 3] :: (List.finRange 14).map (fun k' => [omVar ρ k'])

/-- Substitution for the variables of child `k`: its input variables by `childInput`, its tape
variables by its own block of the parent tape. -/
def childSubst (k : Fin 15) : Fin 4 ⊕ Fin ρ → Poly ρ :=
  Sum.elim (childInput ρ k) (fun i => [[childVar ρ k i]])

/-- Product of two polynomials, expanded into monomials. -/
def polyMul (p q : Poly ρ) : Poly ρ := p.flatMap fun m => q.map fun m' => m ++ m'

/-- Substitute a polynomial for each variable of a polynomial in the child variables and expand. -/
def polySubst (σ : Fin 4 ⊕ Fin ρ → Poly ρ) (p : List (List (Fin 4 ⊕ Fin ρ))) : Poly ρ :=
  p.flatMap fun m => m.foldr (fun v acc => polyMul ρ (σ v) acc) [[]]

end Amplify

/-- The transcript of child `k` inside a parent transcript in `F₂^{15 m}`. -/
def childOut {m : ℕ} (z : Fin (15 * m) → F2) (k : Fin 15) : Fin m → F2 :=
  fun c => z (finProdFinEquiv (k, c))

/-- Construction 3 (RM privacy-amplification step), p. 22, with the decoder of §4.4, p. 23. On input
`(s, w)`: (i) sample a uniform `A ∈ F₂^{3×4}` and compute `s_u = s + A u`; (ii) independently sample a
uniform `(w_u)_{u ∈ I}` with `⊕_u w_u = w`; (iii) independently run `Enc_E` on each child input
`(s_u, w_u)` and output the concatenation of the fifteen child transcripts. The parent tape is
`A` (12 bits), `ω` (14 bits) and the fifteen child tapes; the parent description is obtained from
`E`'s by affine substitution of the child inputs. The decoder "outputs `⊥` if any child decoder does;
otherwise, it XORs the fifteen decoded child values". -/
def amplify (E : Enc4) : Enc4 where
  ρ := 12 + (14 + 15 * E.ρ)
  m := 15 * E.m
  desc := ⟨fun o =>
    let kc := finProdFinEquiv.symm o
    polySubst E.ρ (childSubst E.ρ kc.1) (E.desc.coords kc.2)⟩
  dec := fun z =>
    if h : ∀ k : Fin 15, (E.dec (childOut z k)).isSome then
      some (∑ k : Fin 15, (E.dec (childOut z k)).get (h k))
    else none

end QuadStatRE.Main


