-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_PartialTraces
-- name    : QuantumSepPoly_Frobenius_PartialTraces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:05.040071+00:00
-- url     : https://prove2.me/theorems/9c1f93de-fa86-4fd1-a398-a17ae1736c3b
-- title:
--   Partial traces and the orthogonal projection
-- statement:
--   For $M_{ac,be}$, define $(\operatorname{Tr}_0M)_{ce}=\sum_aM_{ac,ae}$ and $(\operatorname{Tr}_1M)_{ab}=\sum_cM_{ac,bc}$. With $\alpha=\operatorname{Tr}M/d^2$, $A=\operatorname{Tr}_1M/d-\alpha I$, and $B=\operatorname{Tr}_0M/d-\alpha I$, set
--   $$\Pi(M)=M-\operatorname{Tr}_1(M)\otimes I/d-I\otimes\operatorname{Tr}_0(M)/d+\alpha I.$$
--   The centered component is $C=\Pi(M)$. Local rotation is $(U\otimes V)^*M(U\otimes V)$. These are computed formulas, with no vanishing-trace hypothesis on the original input.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), §§2–5, p. 6 (PDF p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_MatrixGeometry

noncomputable section

namespace QuantumSepPoly.Frobenius

/-- §2.1, p.6, equations (3)–(4). -/
def trace0 {d : ℕ} (M : Bip d) : Op d := fun c e => ∑ a, M (a,c) (a,e)
def trace1 {d : ℕ} (M : Bip d) : Op d := fun a b => ∑ c, M (a,c) (b,c)
def tensorOp {d : ℕ} (A B : Op d) : Bip d := fun i j => A i.1 j.1 * B i.2 j.2

def alpha {d : ℕ} (M : Bip d) : ℂ := M.trace / (d : ℂ)^2
def localA {d : ℕ} (M : Bip d) : Op d := (1 / (d : ℂ)) • trace1 M - alpha M • 1
def localB {d : ℕ} (M : Bip d) : Op d := (1 / (d : ℂ)) • trace0 M - alpha M • 1

def project {d : ℕ} (X : Bip d) : Bip d :=
  X - (1 / (d : ℂ)) • tensorOp (trace1 X) 1 -
    (1 / (d : ℂ)) • tensorOp 1 (trace0 X) + alpha X • 1

def centered {d : ℕ} (M : Bip d) : Bip d := project M

def locallyRotate {d : ℕ} (M : Bip d) (U V : Op d) : Bip d :=
  (tensorOp U V).conjTranspose * M * tensorOp U V

end QuantumSepPoly.Frobenius


