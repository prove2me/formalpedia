-- Prove2me | Definitions.Def_CSL_Generated_MemoryAccess_Group09
-- name    : CSL_Generated_MemoryAccess_Group09
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:31:40.664187+00:00
-- url     : https://prove2.me/theorems/7f8785ab-399b-4721-8925-00c16abd7846
-- title:
--   Coded sorting library: Generated / MemoryAccess / Group09
-- statement:
--   Module `CodedSorting.Generated.MemoryAccess.Group09` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.MemoryAccess.Group09

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventChunkData
import Definitions.Def_CSL_Generated_MemoryAccess_Base

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 148. -/
def forwardVisitTree148 : VisitTree := (VisitTree.branch 374 (VisitTree.branch 310 (VisitTree.branch 263 (VisitTree.leaf 256 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 275 (VisitTree.leaf 263 [1, 1, 1, 1, 1]) (VisitTree.leaf 275 [1, 1, 1, 1, 1]))) (VisitTree.branch 325 (VisitTree.leaf 310 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 359 (VisitTree.leaf 325 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 359 [1, 1, 1])))) (VisitTree.branch 410 (VisitTree.branch 392 (VisitTree.leaf 374 [1, 1, 1, 1, 1]) (VisitTree.branch 404 (VisitTree.leaf 392 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 404 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 442 (VisitTree.leaf 410 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 491 (VisitTree.leaf 442 [1, 1, 1, 1]) (VisitTree.leaf 491 [1, 1, 1, 1])))))

def fastForwardChunkVisits148 (r : Nat) : List Nat :=
  forwardVisitTree148.lookup r

private theorem covered148 :
    visitsCovered forwardEventChunk148 forwardVisitTree148 = true := by
  decide +kernel

private theorem checked148 :
    visitsChecked forwardEventChunk148 forwardVisitTree148 = true := by
  decide +kernel

theorem eventVisits_forwardChunk148 (r : Nat) :
    eventVisits r forwardEventChunk148 = fastForwardChunkVisits148 r :=
  eventVisits_of_tree _ _ covered148 checked148 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk148

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 149. -/
def forwardVisitTree149 : VisitTree := (VisitTree.branch 331 (VisitTree.branch 299 (VisitTree.branch 275 (VisitTree.branch 263 (VisitTree.leaf 261 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 263 [1])) (VisitTree.branch 281 (VisitTree.leaf 275 [1]) (VisitTree.leaf 281 [1, 1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 310 (VisitTree.branch 309 (VisitTree.leaf 299 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 309 [1, 1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 329 (VisitTree.leaf 310 [1, 1]) (VisitTree.leaf 329 [1])))) (VisitTree.branch 410 (VisitTree.branch 374 (VisitTree.branch 345 (VisitTree.leaf 331 [1, 1, 1]) (VisitTree.leaf 345 [1, 1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 380 (VisitTree.leaf 374 [1]) (VisitTree.leaf 380 [1, 1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 491 (VisitTree.branch 449 (VisitTree.leaf 410 [1]) (VisitTree.leaf 449 [1, 1])) (VisitTree.branch 492 (VisitTree.leaf 491 [1, 1, 1, 1]) (VisitTree.leaf 492 [1, 1])))))

def fastForwardChunkVisits149 (r : Nat) : List Nat :=
  forwardVisitTree149.lookup r

private theorem covered149 :
    visitsCovered forwardEventChunk149 forwardVisitTree149 = true := by
  decide +kernel

private theorem checked149 :
    visitsChecked forwardEventChunk149 forwardVisitTree149 = true := by
  decide +kernel

theorem eventVisits_forwardChunk149 (r : Nat) :
    eventVisits r forwardEventChunk149 = fastForwardChunkVisits149 r :=
  eventVisits_of_tree _ _ covered149 checked149 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk149

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 150. -/
def forwardVisitTree150 : VisitTree := (VisitTree.branch 343 (VisitTree.branch 331 (VisitTree.branch 249 (VisitTree.leaf 231 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 329 (VisitTree.leaf 249 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 329 [1, 1, 1, 1, 1]))) (VisitTree.branch 339 (VisitTree.leaf 331 [1, 1, 1, 1, 1]) (VisitTree.branch 341 (VisitTree.leaf 339 [1, 1, 1, 1, 1]) (VisitTree.leaf 341 [1, 1, 1, 1])))) (VisitTree.branch 449 (VisitTree.branch 354 (VisitTree.leaf 343 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 375 (VisitTree.leaf 354 [1, 1, 1, 1, 1]) (VisitTree.leaf 375 [1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 456 (VisitTree.leaf 449 [1, 1, 1, 1]) (VisitTree.branch 492 (VisitTree.leaf 456 [1, 1, 1, 1, 1]) (VisitTree.leaf 492 [1, 1, 1, 1, 1])))))

def fastForwardChunkVisits150 (r : Nat) : List Nat :=
  forwardVisitTree150.lookup r

private theorem covered150 :
    visitsCovered forwardEventChunk150 forwardVisitTree150 = true := by
  decide +kernel

private theorem checked150 :
    visitsChecked forwardEventChunk150 forwardVisitTree150 = true := by
  decide +kernel

theorem eventVisits_forwardChunk150 (r : Nat) :
    eventVisits r forwardEventChunk150 = fastForwardChunkVisits150 r :=
  eventVisits_of_tree _ _ covered150 checked150 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk150

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 151. -/
def forwardVisitTree151 : VisitTree := (VisitTree.branch 346 (VisitTree.branch 339 (VisitTree.branch 334 (VisitTree.branch 232 (VisitTree.leaf 231 [1]) (VisitTree.leaf 232 [1, 1, 1])) (VisitTree.branch 338 (VisitTree.leaf 334 [1, 1, 1, 1]) (VisitTree.leaf 338 [1]))) (VisitTree.branch 342 (VisitTree.branch 341 (VisitTree.leaf 339 [1, 1]) (VisitTree.leaf 341 [1, 1, 1, 1])) (VisitTree.branch 343 (VisitTree.leaf 342 [1, 1, 1]) (VisitTree.leaf 343 [1])))) (VisitTree.branch 456 (VisitTree.branch 447 (VisitTree.branch 375 (VisitTree.leaf 346 [1, 1, 1, 1, 1]) (VisitTree.leaf 375 [1])) (VisitTree.branch 455 (VisitTree.leaf 447 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 455 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 461 (VisitTree.branch 457 (VisitTree.leaf 456 [1]) (VisitTree.leaf 457 [1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 481 (VisitTree.leaf 461 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 499 (VisitTree.leaf 481 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 499 [1, 1, 1, 1, 1]))))))

def fastForwardChunkVisits151 (r : Nat) : List Nat :=
  forwardVisitTree151.lookup r

private theorem covered151 :
    visitsCovered forwardEventChunk151 forwardVisitTree151 = true := by
  decide +kernel

private theorem checked151 :
    visitsChecked forwardEventChunk151 forwardVisitTree151 = true := by
  decide +kernel

theorem eventVisits_forwardChunk151 (r : Nat) :
    eventVisits r forwardEventChunk151 = fastForwardChunkVisits151 r :=
  eventVisits_of_tree _ _ covered151 checked151 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk151

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 152. -/
def forwardVisitTree152 : VisitTree := (VisitTree.branch 417 (VisitTree.branch 334 (VisitTree.branch 240 (VisitTree.leaf 232 [1, 1, 1, 1]) (VisitTree.branch 298 (VisitTree.leaf 240 [1, 1]) (VisitTree.leaf 298 [1, 1]))) (VisitTree.branch 342 (VisitTree.branch 338 (VisitTree.leaf 334 [1, 1, 1]) (VisitTree.leaf 338 [1, 1, 1, 1, 1])) (VisitTree.branch 346 (VisitTree.leaf 342 [1, 1]) (VisitTree.leaf 346 [1, 1, 1])))) (VisitTree.branch 482 (VisitTree.branch 425 (VisitTree.branch 423 (VisitTree.leaf 417 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 423 [1, 1, 1, 1, 1])) (VisitTree.branch 437 (VisitTree.leaf 425 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 437 [1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 503 (VisitTree.branch 500 (VisitTree.leaf 482 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 500 [1, 1])) (VisitTree.branch 504 (VisitTree.leaf 503 [1, 1, 1, 1, 1]) (VisitTree.leaf 504 [1, 1, 1, 1, 1])))))

def fastForwardChunkVisits152 (r : Nat) : List Nat :=
  forwardVisitTree152.lookup r

private theorem covered152 :
    visitsCovered forwardEventChunk152 forwardVisitTree152 = true := by
  decide +kernel

private theorem checked152 :
    visitsChecked forwardEventChunk152 forwardVisitTree152 = true := by
  decide +kernel

theorem eventVisits_forwardChunk152 (r : Nat) :
    eventVisits r forwardEventChunk152 = fastForwardChunkVisits152 r :=
  eventVisits_of_tree _ _ covered152 checked152 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk152

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 153. -/
def forwardVisitTree153 : VisitTree := (VisitTree.branch 421 (VisitTree.branch 304 (VisitTree.branch 288 (VisitTree.leaf 240 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 298 (VisitTree.leaf 288 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 298 [1, 1, 1, 1]))) (VisitTree.branch 308 (VisitTree.leaf 304 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 419 (VisitTree.leaf 308 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 419 [1, 1, 1, 1, 1, 1])))) (VisitTree.branch 483 (VisitTree.branch 427 (VisitTree.leaf 421 [1, 1, 1, 1, 1, 1]) (VisitTree.branch 439 (VisitTree.leaf 427 [1, 1, 1, 1, 1]) (VisitTree.leaf 439 [1, 1, 1, 1, 1]))) (VisitTree.branch 500 (VisitTree.leaf 483 [1, 1, 1, 1, 1]) (VisitTree.branch 502 (VisitTree.leaf 500 [1, 1, 1]) (VisitTree.leaf 502 [1, 1, 1, 1, 1])))))

def fastForwardChunkVisits153 (r : Nat) : List Nat :=
  forwardVisitTree153.lookup r

private theorem covered153 :
    visitsCovered forwardEventChunk153 forwardVisitTree153 = true := by
  decide +kernel

private theorem checked153 :
    visitsChecked forwardEventChunk153 forwardVisitTree153 = true := by
  decide +kernel

theorem eventVisits_forwardChunk153 (r : Nat) :
    eventVisits r forwardEventChunk153 = fastForwardChunkVisits153 r :=
  eventVisits_of_tree _ _ covered153 checked153 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk153

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 154. -/
def forwardVisitTree154 : VisitTree := (VisitTree.branch 401 (VisitTree.branch 296 (VisitTree.branch 246 (VisitTree.leaf 242 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 294 (VisitTree.leaf 246 [1, 1, 1]) (VisitTree.leaf 294 [1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 316 (VisitTree.branch 302 (VisitTree.leaf 296 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 302 [1, 1, 1, 1, 1, 1, 1])) (VisitTree.branch 391 (VisitTree.leaf 316 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 391 [1, 1, 1])))) (VisitTree.branch 439 (VisitTree.branch 421 (VisitTree.branch 405 (VisitTree.leaf 401 [1, 1, 1]) (VisitTree.leaf 405 [1])) (VisitTree.branch 427 (VisitTree.leaf 421 [1]) (VisitTree.leaf 427 [1]))) (VisitTree.branch 484 (VisitTree.branch 483 (VisitTree.leaf 439 [1]) (VisitTree.leaf 483 [1, 1, 1])) (VisitTree.branch 501 (VisitTree.leaf 484 [1, 1]) (VisitTree.leaf 501 [1, 1, 1, 1, 1, 1, 1, 1])))))

def fastForwardChunkVisits154 (r : Nat) : List Nat :=
  forwardVisitTree154.lookup r

private theorem covered154 :
    visitsCovered forwardEventChunk154 forwardVisitTree154 = true := by
  decide +kernel

private theorem checked154 :
    visitsChecked forwardEventChunk154 forwardVisitTree154 = true := by
  decide +kernel

theorem eventVisits_forwardChunk154 (r : Nat) :
    eventVisits r forwardEventChunk154 = fastForwardChunkVisits154 r :=
  eventVisits_of_tree _ _ covered154 checked154 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk154

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 155. -/
def forwardVisitTree155 : VisitTree := (VisitTree.branch 276 (VisitTree.branch 266 (VisitTree.branch 246 (VisitTree.leaf 234 [1, 1, 1, 1]) (VisitTree.branch 252 (VisitTree.leaf 246 [1, 1, 1, 1, 1]) (VisitTree.leaf 252 [1, 1, 1, 1]))) (VisitTree.branch 268 (VisitTree.leaf 266 [1, 1, 1, 1, 1]) (VisitTree.branch 272 (VisitTree.leaf 268 [1, 1, 1, 1]) (VisitTree.leaf 272 [1, 1, 1, 1])))) (VisitTree.branch 401 (VisitTree.branch 391 (VisitTree.leaf 276 [1, 1, 1, 1, 1]) (VisitTree.branch 393 (VisitTree.leaf 391 [1, 1, 1, 1, 1]) (VisitTree.leaf 393 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 405 (VisitTree.leaf 401 [1, 1, 1, 1, 1]) (VisitTree.branch 484 (VisitTree.leaf 405 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 484 [1, 1, 1, 1, 1, 1])))))

def fastForwardChunkVisits155 (r : Nat) : List Nat :=
  forwardVisitTree155.lookup r

private theorem covered155 :
    visitsCovered forwardEventChunk155 forwardVisitTree155 = true := by
  decide +kernel

private theorem checked155 :
    visitsChecked forwardEventChunk155 forwardVisitTree155 = true := by
  decide +kernel

theorem eventVisits_forwardChunk155 (r : Nat) :
    eventVisits r forwardEventChunk155 = fastForwardChunkVisits155 r :=
  eventVisits_of_tree _ _ covered155 checked155 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk155

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 156. -/
def forwardVisitTree156 : VisitTree := (VisitTree.branch 272 (VisitTree.branch 253 (VisitTree.branch 235 (VisitTree.branch 234 (VisitTree.leaf 223 [1, 1, 1]) (VisitTree.leaf 234 [1, 1, 1, 1])) (VisitTree.branch 252 (VisitTree.leaf 235 [1, 1]) (VisitTree.leaf 252 [1]))) (VisitTree.branch 266 (VisitTree.branch 260 (VisitTree.leaf 253 [1, 1, 1, 1, 1]) (VisitTree.leaf 260 [1, 1, 1])) (VisitTree.branch 268 (VisitTree.leaf 266 [1]) (VisitTree.leaf 268 [1, 1])))) (VisitTree.branch 389 (VisitTree.branch 276 (VisitTree.branch 274 (VisitTree.leaf 272 [1, 1, 1]) (VisitTree.leaf 274 [1])) (VisitTree.branch 280 (VisitTree.leaf 276 [1]) (VisitTree.leaf 280 [1, 1, 1]))) (VisitTree.branch 399 (VisitTree.branch 397 (VisitTree.leaf 389 [1, 1, 1, 1, 1, 1]) (VisitTree.leaf 397 [1, 1, 1, 1, 1, 1])) (VisitTree.branch 403 (VisitTree.leaf 399 [1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 485 (VisitTree.leaf 403 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 485 [1, 1, 1, 1, 1, 1, 1, 1]))))))

def fastForwardChunkVisits156 (r : Nat) : List Nat :=
  forwardVisitTree156.lookup r

private theorem covered156 :
    visitsCovered forwardEventChunk156 forwardVisitTree156 = true := by
  decide +kernel

private theorem checked156 :
    visitsChecked forwardEventChunk156 forwardVisitTree156 = true := by
  decide +kernel

theorem eventVisits_forwardChunk156 (r : Nat) :
    eventVisits r forwardEventChunk156 = fastForwardChunkVisits156 r :=
  eventVisits_of_tree _ _ covered156 checked156 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk156

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 157. -/
def forwardVisitTree157 : VisitTree := (VisitTree.branch 280 (VisitTree.branch 258 (VisitTree.branch 223 (VisitTree.leaf 222 [1, 1, 1, 1]) (VisitTree.branch 235 (VisitTree.leaf 223 [1, 1, 1, 1, 1]) (VisitTree.leaf 235 [1, 1, 1, 1, 1, 1]))) (VisitTree.branch 260 (VisitTree.leaf 258 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 274 (VisitTree.leaf 260 [1, 1, 1, 1, 1]) (VisitTree.leaf 274 [1, 1, 1, 1, 1, 1, 1])))) (VisitTree.branch 369 (VisitTree.branch 351 (VisitTree.leaf 280 [1, 1, 1, 1, 1]) (VisitTree.branch 353 (VisitTree.leaf 351 [1, 1, 1, 1]) (VisitTree.leaf 353 [1, 1, 1, 1, 1]))) (VisitTree.branch 379 (VisitTree.leaf 369 [1, 1, 1, 1]) (VisitTree.branch 486 (VisitTree.leaf 379 [1, 1, 1, 1, 1]) (VisitTree.leaf 486 [1, 1, 1, 1])))))

def fastForwardChunkVisits157 (r : Nat) : List Nat :=
  forwardVisitTree157.lookup r

private theorem covered157 :
    visitsCovered forwardEventChunk157 forwardVisitTree157 = true := by
  decide +kernel

private theorem checked157 :
    visitsChecked forwardEventChunk157 forwardVisitTree157 = true := by
  decide +kernel

theorem eventVisits_forwardChunk157 (r : Nat) :
    eventVisits r forwardEventChunk157 = fastForwardChunkVisits157 r :=
  eventVisits_of_tree _ _ covered157 checked157 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk157

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 158. -/
def forwardVisitTree158 : VisitTree := (VisitTree.branch 247 (VisitTree.branch 238 (VisitTree.branch 226 (VisitTree.leaf 222 [1, 1]) (VisitTree.branch 236 (VisitTree.leaf 226 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 236 [1, 1, 1, 1, 1, 1, 1, 1]))) (VisitTree.branch 243 (VisitTree.leaf 238 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 244 (VisitTree.leaf 243 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.leaf 244 [1, 1, 1, 1, 1, 1, 1, 1])))) (VisitTree.branch 369 (VisitTree.branch 351 (VisitTree.leaf 247 [1, 1, 1, 1, 1, 1, 1, 1]) (VisitTree.branch 353 (VisitTree.leaf 351 [1, 1, 1, 1]) (VisitTree.leaf 353 [1]))) (VisitTree.branch 379 (VisitTree.leaf 369 [1, 1]) (VisitTree.branch 486 (VisitTree.leaf 379 [1, 1, 1]) (VisitTree.leaf 486 [1, 1, 1, 1])))))

def fastForwardChunkVisits158 (r : Nat) : List Nat :=
  forwardVisitTree158.lookup r

private theorem covered158 :
    visitsCovered forwardEventChunk158 forwardVisitTree158 = true := by
  decide +kernel

private theorem checked158 :
    visitsChecked forwardEventChunk158 forwardVisitTree158 = true := by
  decide +kernel

theorem eventVisits_forwardChunk158 (r : Nat) :
    eventVisits r forwardEventChunk158 = fastForwardChunkVisits158 r :=
  eventVisits_of_tree _ _ covered158 checked158 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk158

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 159. -/
def forwardVisitTree159 : VisitTree := (VisitTree.branch 393 (VisitTree.branch 249 (VisitTree.branch 78 (VisitTree.branch 40 (VisitTree.branch 31 (VisitTree.leaf 12 [1]) (VisitTree.branch 37 (VisitTree.leaf 31 [1]) (VisitTree.leaf 37 [1]))) (VisitTree.branch 45 (VisitTree.leaf 40 [1]) (VisitTree.branch 73 (VisitTree.leaf 45 [1]) (VisitTree.leaf 73 [1])))) (VisitTree.branch 105 (VisitTree.branch 81 (VisitTree.leaf 78 [1]) (VisitTree.branch 86 (VisitTree.leaf 81 [1]) (VisitTree.leaf 86 [1]))) (VisitTree.branch 110 (VisitTree.leaf 105 [1]) (VisitTree.branch 239 (VisitTree.leaf 110 [1]) (VisitTree.leaf 239 [1, 1]))))) (VisitTree.branch 307 (VisitTree.branch 300 (VisitTree.branch 288 (VisitTree.leaf 249 [1, 1]) (VisitTree.branch 289 (VisitTree.leaf 288 [1, 1]) (VisitTree.leaf 289 [1, 1]))) (VisitTree.branch 301 (VisitTree.leaf 300 [1, 1]) (VisitTree.branch 306 (VisitTree.leaf 301 [1, 1]) (VisitTree.leaf 306 [1, 1])))) (VisitTree.branch 382 (VisitTree.branch 316 (VisitTree.leaf 307 [1]) (VisitTree.branch 317 (VisitTree.leaf 316 [1, 1]) (VisitTree.leaf 317 [1, 1]))) (VisitTree.branch 383 (VisitTree.leaf 382 [1]) (VisitTree.branch 392 (VisitTree.leaf 383 [1, 1]) (VisitTree.leaf 392 [1, 1])))))) (VisitTree.branch 649 (VisitTree.branch 460 (VisitTree.branch 410 (VisitTree.branch 398 (VisitTree.leaf 393 [1, 1]) (VisitTree.branch 399 (VisitTree.leaf 398 [1]) (VisitTree.leaf 399 [1, 1]))) (VisitTree.branch 411 (VisitTree.leaf 410 [1, 1]) (VisitTree.branch 451 (VisitTree.leaf 411 [1]) (VisitTree.leaf 451 [1])))) (VisitTree.branch 646 (VisitTree.branch 461 (VisitTree.leaf 460 [1, 1]) (VisitTree.branch 645 (VisitTree.leaf 461 [1, 1]) (VisitTree.leaf 645 [1]))) (VisitTree.branch 647 (VisitTree.leaf 646 [1]) (VisitTree.branch 648 (VisitTree.leaf 647 [1]) (VisitTree.leaf 648 [1]))))) (VisitTree.branch 655 (VisitTree.branch 652 (VisitTree.branch 650 (VisitTree.leaf 649 [1]) (VisitTree.branch 651 (VisitTree.leaf 650 [1]) (VisitTree.leaf 651 [1]))) (VisitTree.branch 653 (VisitTree.leaf 652 [1]) (VisitTree.branch 654 (VisitTree.leaf 653 [1]) (VisitTree.leaf 654 [1])))) (VisitTree.branch 658 (VisitTree.branch 656 (VisitTree.leaf 655 [1]) (VisitTree.branch 657 (VisitTree.leaf 656 [1]) (VisitTree.leaf 657 [1]))) (VisitTree.branch 659 (VisitTree.leaf 658 [1]) (VisitTree.branch 660 (VisitTree.leaf 659 [1]) (VisitTree.leaf 660 [1])))))))

def fastForwardChunkVisits159 (r : Nat) : List Nat :=
  forwardVisitTree159.lookup r

private theorem covered159 :
    visitsCovered forwardEventChunk159 forwardVisitTree159 = true := by
  decide +kernel

private theorem checked159 :
    visitsChecked forwardEventChunk159 forwardVisitTree159 = true := by
  decide +kernel

theorem eventVisits_forwardChunk159 (r : Nat) :
    eventVisits r forwardEventChunk159 = fastForwardChunkVisits159 r :=
  eventVisits_of_tree _ _ covered159 checked159 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk159

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 160. -/
def forwardVisitTree160 : VisitTree := (VisitTree.branch 419 (VisitTree.branch 248 (VisitTree.branch 90 (VisitTree.branch 18 (VisitTree.branch 14 (VisitTree.leaf 8 [1]) (VisitTree.branch 16 (VisitTree.leaf 14 [1]) (VisitTree.leaf 16 [1]))) (VisitTree.branch 20 (VisitTree.leaf 18 [1]) (VisitTree.branch 88 (VisitTree.leaf 20 [1]) (VisitTree.leaf 88 [1])))) (VisitTree.branch 109 (VisitTree.branch 93 (VisitTree.leaf 90 [1]) (VisitTree.branch 95 (VisitTree.leaf 93 [1]) (VisitTree.leaf 95 [1]))) (VisitTree.branch 231 (VisitTree.leaf 109 [1]) (VisitTree.branch 238 (VisitTree.leaf 231 [1, 1]) (VisitTree.leaf 238 [1, 1]))))) (VisitTree.branch 263 (VisitTree.branch 258 (VisitTree.branch 254 (VisitTree.leaf 248 [1]) (VisitTree.branch 255 (VisitTree.leaf 254 [1]) (VisitTree.leaf 255 [1, 1]))) (VisitTree.branch 259 (VisitTree.leaf 258 [1, 1]) (VisitTree.branch 262 (VisitTree.leaf 259 [1]) (VisitTree.leaf 262 [1, 1])))) (VisitTree.branch 414 (VisitTree.branch 266 (VisitTree.leaf 263 [1, 1]) (VisitTree.branch 267 (VisitTree.leaf 266 [1, 1]) (VisitTree.leaf 267 [1, 1]))) (VisitTree.branch 415 (VisitTree.leaf 414 [1, 1]) (VisitTree.branch 418 (VisitTree.leaf 415 [1]) (VisitTree.leaf 418 [1, 1])))))) (VisitTree.branch 633 (VisitTree.branch 450 (VisitTree.branch 428 (VisitTree.branch 424 (VisitTree.leaf 419 [1, 1]) (VisitTree.branch 425 (VisitTree.leaf 424 [1, 1]) (VisitTree.leaf 425 [1, 1]))) (VisitTree.branch 429 (VisitTree.leaf 428 [1]) (VisitTree.branch 447 (VisitTree.leaf 429 [1, 1]) (VisitTree.leaf 447 [1, 1])))) (VisitTree.branch 630 (VisitTree.branch 459 (VisitTree.leaf 450 [1, 1]) (VisitTree.branch 629 (VisitTree.leaf 459 [1]) (VisitTree.leaf 629 [1]))) (VisitTree.branch 631 (VisitTree.leaf 630 [1]) (VisitTree.branch 632 (VisitTree.leaf 631 [1]) (VisitTree.leaf 632 [1]))))) (VisitTree.branch 639 (VisitTree.branch 636 (VisitTree.branch 634 (VisitTree.leaf 633 [1]) (VisitTree.branch 635 (VisitTree.leaf 634 [1]) (VisitTree.leaf 635 [1]))) (VisitTree.branch 637 (VisitTree.leaf 636 [1]) (VisitTree.branch 638 (VisitTree.leaf 637 [1]) (VisitTree.leaf 638 [1])))) (VisitTree.branch 642 (VisitTree.branch 640 (VisitTree.leaf 639 [1]) (VisitTree.branch 641 (VisitTree.leaf 640 [1]) (VisitTree.leaf 641 [1]))) (VisitTree.branch 643 (VisitTree.leaf 642 [1]) (VisitTree.branch 644 (VisitTree.leaf 643 [1]) (VisitTree.leaf 644 [1])))))))

def fastForwardChunkVisits160 (r : Nat) : List Nat :=
  forwardVisitTree160.lookup r

private theorem covered160 :
    visitsCovered forwardEventChunk160 forwardVisitTree160 = true := by
  decide +kernel

private theorem checked160 :
    visitsChecked forwardEventChunk160 forwardVisitTree160 = true := by
  decide +kernel

theorem eventVisits_forwardChunk160 (r : Nat) :
    eventVisits r forwardEventChunk160 = fastForwardChunkVisits160 r :=
  eventVisits_of_tree _ _ covered160 checked160 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk160

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 161. -/
def forwardVisitTree161 : VisitTree := (VisitTree.branch 436 (VisitTree.branch 227 (VisitTree.branch 98 (VisitTree.branch 25 (VisitTree.branch 4 (VisitTree.leaf 2 [1]) (VisitTree.branch 24 (VisitTree.leaf 4 [1]) (VisitTree.leaf 24 [1]))) (VisitTree.branch 28 (VisitTree.leaf 25 [1]) (VisitTree.branch 29 (VisitTree.leaf 28 [1]) (VisitTree.leaf 29 [1])))) (VisitTree.branch 101 (VisitTree.branch 99 (VisitTree.leaf 98 [1]) (VisitTree.branch 100 (VisitTree.leaf 99 [1]) (VisitTree.leaf 100 [1]))) (VisitTree.branch 103 (VisitTree.leaf 101 [1]) (VisitTree.branch 226 (VisitTree.leaf 103 [1]) (VisitTree.leaf 226 [1, 1]))))) (VisitTree.branch 282 (VisitTree.branch 275 (VisitTree.branch 230 (VisitTree.leaf 227 [1]) (VisitTree.branch 274 (VisitTree.leaf 230 [1, 1]) (VisitTree.leaf 274 [1, 1]))) (VisitTree.branch 276 (VisitTree.leaf 275 [1, 1]) (VisitTree.branch 277 (VisitTree.leaf 276 [1, 1]) (VisitTree.leaf 277 [1])))) (VisitTree.branch 285 (VisitTree.branch 283 (VisitTree.leaf 282 [1, 1]) (VisitTree.branch 284 (VisitTree.leaf 283 [1, 1]) (VisitTree.leaf 284 [1]))) (VisitTree.branch 434 (VisitTree.leaf 285 [1, 1]) (VisitTree.branch 435 (VisitTree.leaf 434 [1, 1]) (VisitTree.leaf 435 [1])))))) (VisitTree.branch 617 (VisitTree.branch 446 (VisitTree.branch 439 (VisitTree.branch 437 (VisitTree.leaf 436 [1]) (VisitTree.branch 438 (VisitTree.leaf 437 [1, 1]) (VisitTree.leaf 438 [1, 1]))) (VisitTree.branch 440 (VisitTree.leaf 439 [1, 1]) (VisitTree.branch 441 (VisitTree.leaf 440 [1, 1]) (VisitTree.leaf 441 [1, 1])))) (VisitTree.branch 614 (VisitTree.branch 458 (VisitTree.leaf 446 [1, 1]) (VisitTree.branch 613 (VisitTree.leaf 458 [1, 1]) (VisitTree.leaf 613 [1]))) (VisitTree.branch 615 (VisitTree.leaf 614 [1]) (VisitTree.branch 616 (VisitTree.leaf 615 [1]) (VisitTree.leaf 616 [1]))))) (VisitTree.branch 623 (VisitTree.branch 620 (VisitTree.branch 618 (VisitTree.leaf 617 [1]) (VisitTree.branch 619 (VisitTree.leaf 618 [1]) (VisitTree.leaf 619 [1]))) (VisitTree.branch 621 (VisitTree.leaf 620 [1]) (VisitTree.branch 622 (VisitTree.leaf 621 [1]) (VisitTree.leaf 622 [1])))) (VisitTree.branch 626 (VisitTree.branch 624 (VisitTree.leaf 623 [1]) (VisitTree.branch 625 (VisitTree.leaf 624 [1]) (VisitTree.leaf 625 [1]))) (VisitTree.branch 627 (VisitTree.leaf 626 [1]) (VisitTree.branch 628 (VisitTree.leaf 627 [1]) (VisitTree.leaf 628 [1])))))))

def fastForwardChunkVisits161 (r : Nat) : List Nat :=
  forwardVisitTree161.lookup r

private theorem covered161 :
    visitsCovered forwardEventChunk161 forwardVisitTree161 = true := by
  decide +kernel

private theorem checked161 :
    visitsChecked forwardEventChunk161 forwardVisitTree161 = true := by
  decide +kernel

theorem eventVisits_forwardChunk161 (r : Nat) :
    eventVisits r forwardEventChunk161 = fastForwardChunkVisits161 r :=
  eventVisits_of_tree _ _ covered161 checked161 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk161

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 162. -/
def forwardVisitTree162 : VisitTree := (VisitTree.branch 404 (VisitTree.branch 225 (VisitTree.branch 76 (VisitTree.branch 34 (VisitTree.branch 7 (VisitTree.leaf 1 [1]) (VisitTree.branch 32 (VisitTree.leaf 7 [1]) (VisitTree.leaf 32 [1]))) (VisitTree.branch 39 (VisitTree.leaf 34 [1]) (VisitTree.branch 42 (VisitTree.leaf 39 [1]) (VisitTree.leaf 42 [1])))) (VisitTree.branch 106 (VisitTree.branch 79 (VisitTree.leaf 76 [1]) (VisitTree.branch 85 (VisitTree.leaf 79 [1]) (VisitTree.leaf 85 [1]))) (VisitTree.branch 108 (VisitTree.leaf 106 [1]) (VisitTree.branch 224 (VisitTree.leaf 108 [1]) (VisitTree.leaf 224 [1, 1]))))) (VisitTree.branch 310 (VisitTree.branch 295 (VisitTree.branch 236 (VisitTree.leaf 225 [1, 1]) (VisitTree.branch 237 (VisitTree.leaf 236 [1, 1]) (VisitTree.leaf 237 [1]))) (VisitTree.branch 304 (VisitTree.leaf 295 [1]) (VisitTree.branch 305 (VisitTree.leaf 304 [1, 1]) (VisitTree.leaf 305 [1, 1])))) (VisitTree.branch 389 (VisitTree.branch 311 (VisitTree.leaf 310 [1, 1]) (VisitTree.branch 388 (VisitTree.leaf 311 [1]) (VisitTree.leaf 388 [1, 1]))) (VisitTree.branch 394 (VisitTree.leaf 389 [1, 1]) (VisitTree.branch 395 (VisitTree.leaf 394 [1]) (VisitTree.leaf 395 [1, 1])))))) (VisitTree.branch 601 (VisitTree.branch 456 (VisitTree.branch 409 (VisitTree.branch 405 (VisitTree.leaf 404 [1, 1]) (VisitTree.branch 408 (VisitTree.leaf 405 [1, 1]) (VisitTree.leaf 408 [1, 1]))) (VisitTree.branch 452 (VisitTree.leaf 409 [1, 1]) (VisitTree.branch 453 (VisitTree.leaf 452 [1]) (VisitTree.leaf 453 [1, 1])))) (VisitTree.branch 598 (VisitTree.branch 457 (VisitTree.leaf 456 [1, 1]) (VisitTree.branch 597 (VisitTree.leaf 457 [1, 1]) (VisitTree.leaf 597 [1]))) (VisitTree.branch 599 (VisitTree.leaf 598 [1]) (VisitTree.branch 600 (VisitTree.leaf 599 [1]) (VisitTree.leaf 600 [1]))))) (VisitTree.branch 607 (VisitTree.branch 604 (VisitTree.branch 602 (VisitTree.leaf 601 [1]) (VisitTree.branch 603 (VisitTree.leaf 602 [1]) (VisitTree.leaf 603 [1]))) (VisitTree.branch 605 (VisitTree.leaf 604 [1]) (VisitTree.branch 606 (VisitTree.leaf 605 [1]) (VisitTree.leaf 606 [1])))) (VisitTree.branch 610 (VisitTree.branch 608 (VisitTree.leaf 607 [1]) (VisitTree.branch 609 (VisitTree.leaf 608 [1]) (VisitTree.leaf 609 [1]))) (VisitTree.branch 611 (VisitTree.leaf 610 [1]) (VisitTree.branch 612 (VisitTree.leaf 611 [1]) (VisitTree.leaf 612 [1])))))))

def fastForwardChunkVisits162 (r : Nat) : List Nat :=
  forwardVisitTree162.lookup r

private theorem covered162 :
    visitsCovered forwardEventChunk162 forwardVisitTree162 = true := by
  decide +kernel

private theorem checked162 :
    visitsChecked forwardEventChunk162 forwardVisitTree162 = true := by
  decide +kernel

theorem eventVisits_forwardChunk162 (r : Nat) :
    eventVisits r forwardEventChunk162 = fastForwardChunkVisits162 r :=
  eventVisits_of_tree _ _ covered162 checked162 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk162

namespace CSL.Construction.PhysicalFramePaths
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 163. -/
def forwardVisitTree163 : VisitTree := (VisitTree.branch 371 (VisitTree.branch 251 (VisitTree.branch 87 (VisitTree.branch 60 (VisitTree.branch 13 (VisitTree.leaf 10 [1]) (VisitTree.branch 50 (VisitTree.leaf 13 [1]) (VisitTree.leaf 50 [1]))) (VisitTree.branch 67 (VisitTree.leaf 60 [1]) (VisitTree.branch 83 (VisitTree.leaf 67 [1]) (VisitTree.leaf 83 [1])))) (VisitTree.branch 244 (VisitTree.branch 104 (VisitTree.leaf 87 [1]) (VisitTree.branch 107 (VisitTree.leaf 104 [1]) (VisitTree.leaf 107 [1]))) (VisitTree.branch 245 (VisitTree.leaf 244 [1, 1]) (VisitTree.branch 250 (VisitTree.leaf 245 [1]) (VisitTree.leaf 250 [1]))))) (VisitTree.branch 331 (VisitTree.branch 294 (VisitTree.branch 290 (VisitTree.leaf 251 [1, 1]) (VisitTree.branch 291 (VisitTree.leaf 290 [1]) (VisitTree.leaf 291 [1, 1]))) (VisitTree.branch 303 (VisitTree.leaf 294 [1, 1]) (VisitTree.branch 330 (VisitTree.leaf 303 [1, 1]) (VisitTree.leaf 330 [1, 1])))) (VisitTree.branch 352 (VisitTree.branch 334 (VisitTree.leaf 331 [1, 1]) (VisitTree.branch 335 (VisitTree.leaf 334 [1, 1]) (VisitTree.leaf 335 [1, 1]))) (VisitTree.branch 353 (VisitTree.leaf 352 [1]) (VisitTree.branch 370 (VisitTree.leaf 353 [1, 1]) (VisitTree.leaf 370 [1])))))) (VisitTree.branch 584 (VisitTree.branch 454 (VisitTree.branch 413 (VisitTree.branch 390 (VisitTree.leaf 371 [1]) (VisitTree.branch 391 (VisitTree.leaf 390 [1]) (VisitTree.leaf 391 [1, 1]))) (VisitTree.branch 448 (VisitTree.leaf 413 [1]) (VisitTree.branch 449 (VisitTree.leaf 448 [1, 1]) (VisitTree.leaf 449 [1, 1])))) (VisitTree.branch 581 (VisitTree.branch 455 (VisitTree.leaf 454 [1, 1]) (VisitTree.branch 580 (VisitTree.leaf 455 [1, 1]) (VisitTree.leaf 580 [1]))) (VisitTree.branch 582 (VisitTree.leaf 581 [1]) (VisitTree.branch 583 (VisitTree.leaf 582 [1]) (VisitTree.leaf 583 [1]))))) (VisitTree.branch 590 (VisitTree.branch 587 (VisitTree.branch 585 (VisitTree.leaf 584 [1]) (VisitTree.branch 586 (VisitTree.leaf 585 [1]) (VisitTree.leaf 586 [1]))) (VisitTree.branch 588 (VisitTree.leaf 587 [1]) (VisitTree.branch 589 (VisitTree.leaf 588 [1]) (VisitTree.leaf 589 [1])))) (VisitTree.branch 593 (VisitTree.branch 591 (VisitTree.leaf 590 [1]) (VisitTree.branch 592 (VisitTree.leaf 591 [1]) (VisitTree.leaf 592 [1]))) (VisitTree.branch 595 (VisitTree.branch 594 (VisitTree.leaf 593 [1]) (VisitTree.leaf 594 [1])) (VisitTree.branch 596 (VisitTree.leaf 595 [1]) (VisitTree.leaf 596 [1])))))))

def fastForwardChunkVisits163 (r : Nat) : List Nat :=
  forwardVisitTree163.lookup r

private theorem covered163 :
    visitsCovered forwardEventChunk163 forwardVisitTree163 = true := by
  decide +kernel

private theorem checked163 :
    visitsChecked forwardEventChunk163 forwardVisitTree163 = true := by
  decide +kernel

theorem eventVisits_forwardChunk163 (r : Nat) :
    eventVisits r forwardEventChunk163 = fastForwardChunkVisits163 r :=
  eventVisits_of_tree _ _ covered163 checked163 r

end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk163


