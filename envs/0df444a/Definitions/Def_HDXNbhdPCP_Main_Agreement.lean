-- Prove2me | Definitions.Def_HDXNbhdPCP_Main_Agreement
-- name    : HDXNbhdPCP_Main_Agreement
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:58:53.009907+00:00
-- url     : https://prove2.me/theorems/04ac6f6d-e9de-417b-aae9-3b3def3b6a91
-- title:
--   Agreement tests, local ensembles, $\mathrm{Agr}$, $\eta$-edge support, $(\varepsilon_0,\eta,c,e)$-soundness, projectivity, the neighbourhood test (Definitions 1.2, 2.15-2.17, 3.1)
-- statement:
--   An **agreement test** $T=(U,\mathcal S,\pi)$ (Definition 2.15) consists of a finite universe $U$, sets $S_q\subseteq U$ indexed by $q\in Q$, and a distribution $\pi$ over triples $(B,S_1,S_2)$ with $\emptyset\ne B\subseteq S_1\cap S_2$. Each set carries the distribution with which distances on it are measured: uniform, or, for a face set of a weighted complex, its induced distribution (§2.4). For $D$ a set with a distribution, $\mathrm{dist}_D(f,g)=\Pr_{x\sim D}[f(x)\ne g(x)]$.
--
--   A **local ensemble** is $F=(f_q:S_q\to\Sigma)_q$ for a finite alphabet $\Sigma$.
--
--   1. The agreement probability is $\mathrm{Agr}_T(F)=\Pr_{(B,S_1,S_2)\sim\pi}[f_{S_1}\equiv_B f_{S_2}]$ (2.1).
--   2. The $\eta$-edge support of a global $g:U\to\Sigma$ is
--   $$\mathrm{supp}^\eta_T(F,g)=\Pr_{(B,S_1,S_2)\sim\pi}\big[f_{S_1}\equiv_B f_{S_2}\text{ and }\mathrm{dist}_{S_i}(f_{S_i},g)\le\eta,\ i=1,2\big]\quad(2.2).$$
--   3. For $\varepsilon_0,\eta\in[0,1]$ and $c,e>0$, $T$ is **$(\varepsilon_0,\eta,c,e)$-sound** (Definition 2.17) if for every nonempty finite alphabet $\Sigma$ and every $F$ with $\mathrm{Agr}_T(F)>\varepsilon_0$ there is $g:U\to\Sigma$ with $\mathrm{supp}^\eta_T(F,g)>c\,\mathrm{Agr}_T(F)^e$.
--   4. $T$ is **projective** (Definition 2.16) if every triple in the support of $\pi$ has $B=S_1$ or $B=S_2$.
--   5. For a list $L$ of global functions, $\mathrm{supp}_\gamma(L)$ is the probability that the test passes and both endpoint functions are $\gamma$-close to the same member of $L$ (Lemma 6.12).
--
--   The **neighbourhood test** (Definition 3.1) on a 3-partite complex $X=(X[1],X[2],X[3])$ has universe $X[2]$, one set $X_u[2]$ (with its link distribution) for every $u\in X[1]\cup X[3]$, and samples $(u,v)\sim X[1,3]$, comparing $f_u$ and $f_v$ on $B=X_{uv}[2]$. Its **$\zeta$-approximate** version (§3.4, Appendix C) accepts when $\mathrm{dist}_{X_{uv}[2]}(f_u,f_v)\le\zeta$; $\mathrm{Agr}_\zeta(F)$ is its acceptance probability. The vertex distribution of $X[1,3]$ picks a uniform colour in $\{1,3\}$ and then a vertex.
--
--   These definitions carry the agreement-testing statements of the mission (Lemma 3.11, Theorem 3.2, Lemma 6.10–6.12, Theorem 6.1).
--
--   **Formalization Note** The test is stated on three chosen colours $c_1,c_2,c_3$ of any complex `K`; on a 3-partite complex with $(c_1,c_2,c_3)=(0,1,2)$ it is the paper's test, and on a larger complex it is the test on the colour restriction $K[c_1,c_2,c_3]$. A local function $f_q$ is a function on the whole vertex type of colour $c_2$; only its values on $S_q$ are ever read. The alphabet quantifier in soundness ranges over all `Sig : Type` with `Fintype` and `Nonempty`.
-- source:
--   Dikstein, Dinur, Hopkins, Singer, Sounder, shorter, and simpler PCPs from HDX neighborhoods, STOC 2027 submission (manuscript sha256 7dcb1b53…), p. 5, Definition 1.2; p. 16, Definitions 2.15-2.17 and (2.1)-(2.2); p. 18, Definition 3.1; p. 22, §3.4; p. 64, Appendix C

import Mathlib
import Definitions.Def_HDXNbhdPCP_Main_Complex

/-!
# Agreement tests and the neighbourhood test (Dikstein–Dinur–Hopkins–Singer, §1.1, §2.4, §3)

* `AgreementTest U Q` (Definition 2.15): sets `S_Q ⊆ U` indexed by `Q`, each carrying the
  distribution with which distances on it are measured, and a distribution `π` over triples
  `(B, Q₁, Q₂)`.
* `Agr` (2.1), the `η`-edge support `edgeSupp` (2.2), `(ε₀, η, c, e)`-soundness `IsSound`
  (Definition 2.17), projectivity `IsProjective` (Definition 2.16).
* `nbhdTestOn K c₁ c₂ c₃` : the neighbourhood test (Definition 3.1) on the 3-partite colour
  restriction `K[c₁, c₂, c₃]`.
* `approxAgr` : acceptance of the `ζ`-approximate neighbourhood test (§3.4, Appendix C).
-/

namespace HDXNbhdPCP.Main

open Classical

noncomputable section

/-- Definition 2.15: an agreement test. `S q` is the set `S_q ⊆ U` (its support) together with
the distribution used to measure distances on it (uniform, or the induced distribution of a face
set); `pi` is the test distribution over triples `(B, q₁, q₂)` with `∅ ≠ B ⊆ S_{q₁} ∩ S_{q₂}`. -/
structure AgreementTest (U Q : Type) where
  /-- the sets of the test, with their distributions -/
  S : Q → FinDist U
  /-- the test distribution over triples `(B, q₁, q₂)` -/
  pi : FinDist (Finset U × Q × Q)

namespace AgreementTest

variable {U Q : Type}

/-- The local functions `f_{q₁}` and `f_{q₂}` agree on the comparison set `B`. -/
def agreeOn {Sig : Type} (F : Q → U → Sig) (t : Finset U × Q × Q) : Prop :=
  ∀ x ∈ t.1, F t.2.1 x = F t.2.2 x

/-- `dist_D(f, g) = P_{x ∼ D}[f(x) ≠ g(x)]`. -/
def distOn {Sig : Type} (D : FinDist U) (f g : U → Sig) : ℝ :=
  D.prob (fun x => f x ≠ g x)

/-- (2.1): the agreement probability `Agr_T(F) = P_{(B,S₁,S₂) ∼ π}[f_{S₁} ≡_B f_{S₂}]` of a local
ensemble `F = (f_q)_q` (only the values of `f_q` on `S_q` matter). -/
def Agr {Sig : Type} (T : AgreementTest U Q) (F : Q → U → Sig) : ℝ :=
  T.pi.prob (agreeOn F)

/-- (2.2): the `η`-edge support of a global function `g`:
`P[f_{S₁} ≡_B f_{S₂} and dist_{S_i}(f_{S_i}, g) ≤ η for i = 1, 2]`. -/
def edgeSupp {Sig : Type} (T : AgreementTest U Q) (F : Q → U → Sig) (g : U → Sig) (η : ℝ) : ℝ :=
  T.pi.prob (fun t => agreeOn F t ∧ distOn (T.S t.2.1) (F t.2.1) g ≤ η ∧
    distOn (T.S t.2.2) (F t.2.2) g ≤ η)

/-- The probability that the test passes and both endpoint functions are `γ`-close to the same
member of the list `L` (the quantity `supp_γ(L)` of Lemma 6.12). -/
def listSupp {Sig : Type} (T : AgreementTest U Q) (F : Q → U → Sig) (L : List (U → Sig))
    (γ : ℝ) : ℝ :=
  T.pi.prob (fun t => agreeOn F t ∧ ∃ g ∈ L, distOn (T.S t.2.1) (F t.2.1) g ≤ γ ∧
    distOn (T.S t.2.2) (F t.2.2) g ≤ γ)

/-- Definition 2.17: for `ε₀, η ∈ [0,1]` and `c, e > 0`, `T` is `(ε₀, η, c, e)`-sound if for
every nonempty finite alphabet `Σ` and every local ensemble `F` with `Agr_T(F) > ε₀` there is a
global function `g : U → Σ` with `supp^η_T(F, g) > c · Agr_T(F)^e`. -/
def IsSound (T : AgreementTest U Q) (ε₀ η c e : ℝ) : Prop :=
  0 ≤ ε₀ ∧ ε₀ ≤ 1 ∧ 0 ≤ η ∧ η ≤ 1 ∧ 0 < c ∧ 0 < e ∧
    ∀ (Sig : Type) [Fintype Sig] [Nonempty Sig] (F : Q → U → Sig),
      T.Agr F > ε₀ → ∃ g : U → Sig, T.edgeSupp F g η > c * T.Agr F ^ e

/-- Definition 2.16: every triple `(B, S₁, S₂)` in the support of `π` has `B = S₁` or `B = S₂`. -/
def IsProjective (T : AgreementTest U Q) : Prop :=
  ∀ t ∈ T.pi.supp, t.1 = (T.S t.2.1).supp ∨ t.1 = (T.S t.2.2).supp

end AgreementTest

namespace ColoredComplex

variable {I : Type} {V : I → Type}

/-- The link distribution `X_u[c₂]` of a colour-`c₁` vertex `u`. -/
def linkDist₁ (K : ColoredComplex I V) (c₁ c₂ : I) (u : V c₁) : FinDist (V c₂) :=
  FinDist.map (FinDist.cond K (fun x => x c₁ = u)) (fun x => x c₂)

/-- The edge-link distribution `X_{uv}[c₂]` of an edge `(u, v)` of colours `(c₁, c₃)`. -/
def edgeLinkDist (K : ColoredComplex I V) (c₁ c₂ c₃ : I) (u : V c₁) (v : V c₃) :
    FinDist (V c₂) :=
  FinDist.map (FinDist.cond K (fun x => x c₁ = u ∧ x c₃ = v)) (fun x => x c₂)

/-- Definition 3.1: the neighbourhood test on the 3-partite complex `X = K[c₁, c₂, c₃]`
(colours `1, 2, 3` of the paper are `c₁, c₂, c₃`): universe `X[2]`; one set `X_u[2]` (with its link
distribution) for each `u ∈ X[1] ⊔ X[3]`; the test samples `(u, v) ∼ X[1, 3]` and compares `f_u`
and `f_v` on `B = X_{uv}[2]`. -/
def nbhdTestOn (K : ColoredComplex I V) (c₁ c₂ c₃ : I) :
    AgreementTest (V c₂) (V c₁ ⊕ V c₃) where
  S q := match q with
    | Sum.inl u => K.linkDist₁ c₁ c₂ u
    | Sum.inr v => K.linkDist₁ c₃ c₂ v
  pi := FinDist.map K (fun x =>
    ((K.edgeLinkDist c₁ c₂ c₃ (x c₁) (x c₃)).supp, Sum.inl (x c₁), Sum.inr (x c₃)))

/-- The acceptance probability `Agr_ζ(F)` of the `ζ`-approximate neighbourhood test on
`K[c₁, c₂, c₃]` (§3.4, Appendix C): sample `(u, v) ∼ X[1, 3]` and accept when
`dist_{X_{uv}[2]}(f_u, f_v) ≤ ζ`. -/
def approxAgr {Sig : Type} (K : ColoredComplex I V) (c₁ c₂ c₃ : I)
    (F : V c₁ ⊕ V c₃ → V c₂ → Sig) (ζ : ℝ) : ℝ :=
  K.prob (fun x => AgreementTest.distOn (K.edgeLinkDist c₁ c₂ c₃ (x c₁) (x c₃))
    (F (Sum.inl (x c₁))) (F (Sum.inr (x c₃))) ≤ ζ)

/-- The vertex distribution of the two-colour complex `K[c₁, c₃]` (its `0`-faces): a uniform colour
in `{c₁, c₃}`, then a vertex of that colour. -/
def outerVertexDist (K : ColoredComplex I V) (c₁ c₃ : I) : FinDist (V c₁ ⊕ V c₃) :=
  FinDist.mixUniform (Finset.univ : Finset Bool) (fun b =>
    if b then FinDist.map K (fun x => (Sum.inl (x c₁) : V c₁ ⊕ V c₃))
    else FinDist.map K (fun x => (Sum.inr (x c₃) : V c₁ ⊕ V c₃)))

end ColoredComplex

end

end HDXNbhdPCP.Main


